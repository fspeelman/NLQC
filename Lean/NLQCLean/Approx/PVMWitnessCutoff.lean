import NLQCLean.Approx.SlimWitnessDifferential
import NLQCLean.Rigidity.PVMExtendedDifferential
import NLQCLean.Approx.PVMWitnessVelocityBounds
import NLQCLean.Bounds.NearBellWitnessCover

/-!
# The strong measurement cutoff (`lem:bell-cutoff`)

At a valid PVM witness the Frobenius velocities obey
`‖Ė‖ + ‖Ḋ‖ ≤ √(2d² + 2d² r + 2S) ‖v‖` in the normalized block coordinates. The reverse
velocity uses `‖(X ⊗ J)C_γ‖_F ≤ ‖X‖_F`: the compressed flag is block diagonal with unit blocks
`γ_i`. For near-Bell shapes with `d³ ≤ 2K` the coefficient is at most `4√K`, and splitting the
two leakage residuals at singular value `8δ` gives `dT̂ = T + R` with
`rank T ≤ 4d² − 3 + 4d²⌊d²/64⌋`, `‖dT̂‖ ≤ 4√K` and `‖R‖ ≤ 32δ√K`, exactly as for the
near-SWAP witnesses. The cutoffs are chosen pointwise.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

section Flag

variable {δ : Type*} [Fintype δ] [DecidableEq δ] {s : δ → ℕ}

omit [Fintype δ] in
theorem compressedFlag_apply_of_ne_left (g : ∀ i, Fin (s i) × Fin (s i) → ℂ)
    {p q : FlagSupport s} {i : δ} (h : p.1 ≠ i) : compressedFlag g (p, q) i = 0 := by
  simp [compressedFlag, h]

omit [Fintype δ] in
theorem compressedFlag_apply_of_ne_right (g : ∀ i, Fin (s i) × Fin (s i) → ℂ)
    {p q : FlagSupport s} {i : δ} (h : q.1 ≠ i) : compressedFlag g (p, q) i = 0 := by
  by_cases hp : p.1 = i
  · simp [compressedFlag, hp, h]
  · simp [compressedFlag, hp]

/-- The `i`-th column block of a matrix on the flagged support. -/
def flagBlock {l : Type*} (X : Matrix l (FlagSupport s) ℂ) (i : δ) : Matrix l (Fin (s i)) ℂ :=
  Matrix.of fun a k => X a ⟨i, k⟩

omit [DecidableEq δ] in
theorem sum_frobNorm_flagBlock_sq {l : Type*} [Fintype l] (X : Matrix l (FlagSupport s) ℂ) :
    ∑ i, ‖flagBlock X i‖ ^ 2 = ‖X‖ ^ 2 := by
  simp only [frobNorm_sq, flagBlock, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_sigma]

theorem kronecker_one_mul_compressedFlag_apply {l : Type*} [Fintype l]
    (X : Matrix l (FlagSupport s) ℂ) (g : ∀ i, Fin (s i) × Fin (s i) → ℂ)
    (a : l) (k : δ) (b : Fin (s k)) :
    ((X ⊗ₖ (1 : Matrix (FlagSupport s) (FlagSupport s) ℂ)) * compressedFlag g) (a, ⟨k, b⟩) k =
      ∑ c : Fin (s k), X a ⟨k, c⟩ * g k (c, b) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    exact Finset.sum_eq_zero fun c _ => by
      rw [compressedFlag_apply_of_ne_left g (by simpa using hj), mul_zero]
  · simp

theorem kronecker_one_mul_compressedFlag_apply_of_ne {l : Type*} [Fintype l]
    (X : Matrix l (FlagSupport s) ℂ) (g : ∀ i, Fin (s i) × Fin (s i) → ℂ)
    (a : l) (q : FlagSupport s) (k : δ) (hq : q.1 ≠ k) :
    ((X ⊗ₖ (1 : Matrix (FlagSupport s) (FlagSupport s) ℂ)) * compressedFlag g) (a, q) k = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Matrix.kroneckerMap_apply, Matrix.one_apply]
  split_ifs with h
  · subst h; rw [compressedFlag_apply_of_ne_right g hq, mul_zero]
  · simp

/-- `‖(X ⊗ 1) C_γ‖_F ≤ ‖X‖_F` for unit garbage vectors. -/
theorem frobNorm_kronecker_one_mul_compressedFlag_le {l : Type*} [Fintype l]
    (X : Matrix l (FlagSupport s) ℂ) {g : ∀ i, Fin (s i) × Fin (s i) → ℂ}
    (hg : ∀ i, IsUnitVector (g i)) :
    ‖(X ⊗ₖ (1 : Matrix (FlagSupport s) (FlagSupport s) ℂ)) * compressedFlag g‖ ≤ ‖X‖ := by
  set M := (X ⊗ₖ (1 : Matrix (FlagSupport s) (FlagSupport s) ℂ)) * compressedFlag g with hM
  have hrow : ∀ (a : l) (j : δ) (b : Fin (s j)),
      ∑ k, ‖M (a, ⟨j, b⟩) k‖ ^ 2 = ‖∑ c : Fin (s j), X a ⟨j, c⟩ * g j (c, b)‖ ^ 2 := by
    intro a j b
    rw [Finset.sum_eq_single j]
    · rw [hM, kronecker_one_mul_compressedFlag_apply]
    · intro k _ hk
      rw [hM, kronecker_one_mul_compressedFlag_apply_of_ne _ _ _ _ _ (Ne.symm hk)]
      simp
    · simp
  have hsq : ‖M‖ ^ 2 = ∑ k, ‖flagBlock X k * resourceMatrix (g k)‖ ^ 2 := by
    calc ‖M‖ ^ 2 = ∑ a, ∑ j, ∑ b : Fin (s j), ∑ k, ‖M (a, ⟨j, b⟩) k‖ ^ 2 := by
          rw [frobNorm_sq, Fintype.sum_prod_type]
          simp_rw [Fintype.sum_sigma]
      _ = ∑ a, ∑ j, ∑ b : Fin (s j), ‖∑ c : Fin (s j), X a ⟨j, c⟩ * g j (c, b)‖ ^ 2 := by
          simp_rw [hrow]
      _ = ∑ j, ∑ a, ∑ b : Fin (s j), ‖∑ c : Fin (s j), X a ⟨j, c⟩ * g j (c, b)‖ ^ 2 :=
          Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [frobNorm_sq]
          simp [Matrix.mul_apply, flagBlock, resourceMatrix_apply]
  have hblock : ∀ k, ‖flagBlock X k * resourceMatrix (g k)‖ ^ 2 ≤ ‖flagBlock X k‖ ^ 2 := by
    intro k
    have hR : ‖resourceMatrix (g k)‖ = 1 := (isUnitVector_iff_norm_resourceMatrix _).mp (hg k)
    have h := (frobNorm_mul_le' (flagBlock X k) (resourceMatrix (g k))).trans
      (mul_le_mul_of_nonneg_left ((opNorm_le_frobNorm _).trans hR.le) (norm_nonneg _))
    rw [mul_one] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have h2 : ‖M‖ ^ 2 ≤ ‖X‖ ^ 2 := by
    rw [hsq, ← sum_frobNorm_flagBlock_sq]
    exact Finset.sum_le_sum fun k _ => hblock k
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

theorem one_kronecker_mul_compressedFlag_apply {l : Type*} [Fintype l]
    (Y : Matrix l (FlagSupport s) ℂ) (g : ∀ i, Fin (s i) × Fin (s i) → ℂ)
    (k : δ) (b : Fin (s k)) (a : l) :
    (((1 : Matrix (FlagSupport s) (FlagSupport s) ℂ) ⊗ₖ Y) * compressedFlag g) (⟨k, b⟩, a) k =
      ∑ c : Fin (s k), Y a ⟨k, c⟩ * g k (b, c) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single (⟨k, b⟩ : FlagSupport s)]
  · simp only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, one_mul]
    rw [Fintype.sum_sigma, Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      exact Finset.sum_eq_zero fun c _ => by
        rw [compressedFlag_apply_of_ne_right g (by simpa using hj), mul_zero]
    · simp
  · intro p _ hp
    exact Finset.sum_eq_zero fun q _ => by
      rw [Matrix.kroneckerMap_apply, Matrix.one_apply_ne (Ne.symm hp), zero_mul, zero_mul]
  · simp

theorem one_kronecker_mul_compressedFlag_apply_of_ne {l : Type*} [Fintype l]
    (Y : Matrix l (FlagSupport s) ℂ) (g : ∀ i, Fin (s i) × Fin (s i) → ℂ)
    (p : FlagSupport s) (a : l) (k : δ) (hp : p.1 ≠ k) :
    (((1 : Matrix (FlagSupport s) (FlagSupport s) ℂ) ⊗ₖ Y) * compressedFlag g) (p, a) k = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [Matrix.kroneckerMap_apply, Matrix.one_apply]
  split_ifs with h
  · subst h; rw [compressedFlag_apply_of_ne_left g hp, mul_zero]
  · simp

/-- `‖(1 ⊗ Y) C_γ‖_F ≤ ‖Y‖_F` for unit garbage vectors. -/
theorem frobNorm_one_kronecker_mul_compressedFlag_le {l : Type*} [Fintype l]
    (Y : Matrix l (FlagSupport s) ℂ) {g : ∀ i, Fin (s i) × Fin (s i) → ℂ}
    (hg : ∀ i, IsUnitVector (g i)) :
    ‖((1 : Matrix (FlagSupport s) (FlagSupport s) ℂ) ⊗ₖ Y) * compressedFlag g‖ ≤ ‖Y‖ := by
  set M := ((1 : Matrix (FlagSupport s) (FlagSupport s) ℂ) ⊗ₖ Y) * compressedFlag g with hM
  have hrow : ∀ (j : δ) (b : Fin (s j)) (a : l),
      ∑ k, ‖M (⟨j, b⟩, a) k‖ ^ 2 = ‖∑ c : Fin (s j), Y a ⟨j, c⟩ * g j (b, c)‖ ^ 2 := by
    intro j b a
    rw [Finset.sum_eq_single j]
    · rw [hM, one_kronecker_mul_compressedFlag_apply]
    · intro k _ hk
      rw [hM, one_kronecker_mul_compressedFlag_apply_of_ne _ _ _ _ _ (Ne.symm hk)]
      simp
    · simp
  have hsq : ‖M‖ ^ 2 = ∑ k, ‖flagBlock Y k * (resourceMatrix (g k))ᵀ‖ ^ 2 := by
    calc ‖M‖ ^ 2 = ∑ j, ∑ b : Fin (s j), ∑ a, ∑ k, ‖M (⟨j, b⟩, a) k‖ ^ 2 := by
          rw [frobNorm_sq, Fintype.sum_prod_type, Fintype.sum_sigma]
      _ = ∑ j, ∑ b : Fin (s j), ∑ a, ‖∑ c : Fin (s j), Y a ⟨j, c⟩ * g j (b, c)‖ ^ 2 := by
          simp_rw [hrow]
      _ = _ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [frobNorm_sq, Finset.sum_comm]
          simp [Matrix.mul_apply, flagBlock, resourceMatrix_apply]
  have hblock : ∀ k, ‖flagBlock Y k * (resourceMatrix (g k))ᵀ‖ ^ 2 ≤ ‖flagBlock Y k‖ ^ 2 := by
    intro k
    have hR : ‖(resourceMatrix (g k))ᵀ‖ = 1 := by
      rw [Matrix.frobenius_norm_transpose]
      exact (isUnitVector_iff_norm_resourceMatrix _).mp (hg k)
    have h := (frobNorm_mul_le' (flagBlock Y k) (resourceMatrix (g k))ᵀ).trans
      (mul_le_mul_of_nonneg_left ((opNorm_le_frobNorm _).trans hR.le) (norm_nonneg _))
    rw [mul_one] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have h2 : ‖M‖ ^ 2 ≤ ‖Y‖ ^ 2 := by
    rw [hsq, ← sum_frobNorm_flagBlock_sq]
    exact Finset.sum_le_sum fun k _ => hblock k
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

/-- With an isometric right factor: `‖(X ⊗ J) C_γ‖_F ≤ ‖X‖_F`. -/
theorem frobNorm_kronecker_isometry_right_mul_compressedFlag_le {l lB : Type*} [Fintype l]
    [DecidableEq l] [Fintype lB] [DecidableEq lB] (X : Matrix l (FlagSupport s) ℂ)
    {J : Matrix lB (FlagSupport s) ℂ} (hJ : IsIsometry J) {g : ∀ i, Fin (s i) × Fin (s i) → ℂ}
    (hg : ∀ i, IsUnitVector (g i)) : ‖(X ⊗ₖ J) * compressedFlag g‖ ≤ ‖X‖ := by
  have hfact : X ⊗ₖ J = ((1 : Matrix l l ℂ) ⊗ₖ J) *
      (X ⊗ₖ (1 : Matrix (FlagSupport s) (FlagSupport s) ℂ)) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  rw [hfact, Matrix.mul_assoc, (isIsometry_one.kronecker hJ).frobNorm_mul_eq]
  exact frobNorm_kronecker_one_mul_compressedFlag_le X hg

/-- With an isometric left factor: `‖(J ⊗ Y) C_γ‖_F ≤ ‖Y‖_F`. -/
theorem frobNorm_kronecker_isometry_left_mul_compressedFlag_le {l lA : Type*} [Fintype l]
    [Fintype lA] [DecidableEq lA] [DecidableEq l] (Y : Matrix l (FlagSupport s) ℂ)
    {J : Matrix lA (FlagSupport s) ℂ} (hJ : IsIsometry J) {g : ∀ i, Fin (s i) × Fin (s i) → ℂ}
    (hg : ∀ i, IsUnitVector (g i)) : ‖(J ⊗ₖ Y) * compressedFlag g‖ ≤ ‖Y‖ := by
  have hfact : J ⊗ₖ Y = (J ⊗ₖ (1 : Matrix l l ℂ)) *
      ((1 : Matrix (FlagSupport s) (FlagSupport s) ℂ) ⊗ₖ Y) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  rw [hfact, Matrix.mul_assoc, (hJ.kronecker isIsometry_one).frobNorm_mul_eq]
  exact frobNorm_one_kronecker_mul_compressedFlag_le Y hg

end Flag

namespace PVMReverseBlocks

variable {d K : ℕ} {s : PVMReverseShape d K}

theorem IsValid.frobNorm_forwardVelocity_le {x : PVMReverseBlocks s} (hx : IsValid x)
    (v : PVMReverseBlocks s) :
    ‖forwardVelocity x v‖ ≤
      Real.sqrt d * ‖v.2.2.2.1‖ + Real.sqrt d * ‖v.2.2.1‖ + d * ‖WithLp.toLp 2 v.1‖ := by
  have hE := s.isIsometry_rowEmbeddingA.kronecker s.isIsometry_rowEmbeddingB
  rw [forwardVelocity, hE.frobNorm_mul_eq, encodedStateVelocity,
    (isIsometry_exchangeMatrix _ _ _ _).frobNorm_mul_eq, Matrix.add_mul]
  have h1 := frobNorm_kronecker_isometry_left_mul_insertResource_le (a := Fin d) (b := Fin d)
    hx.2.2.1 v.2.2.2.1 hx.1
  have h2 := frobNorm_kronecker_isometry_right_mul_insertResource_le (a := Fin d) (b := Fin d)
    v.2.2.1 hx.2.2.2.1 hx.1
  have h3 : ‖(x.2.2.1 ⊗ₖ x.2.2.2.1) * insertResource (Fin d) (Fin d) v.1‖ =
      d * ‖WithLp.toLp 2 v.1‖ := by
    rw [(hx.2.2.1.kronecker hx.2.2.2.1).frobNorm_mul_eq, norm_insertResource]
    simp [Fintype.card_prod, Fintype.card_fin, Real.sqrt_mul_self (Nat.cast_nonneg d)]
  simp only [Fintype.card_fin] at h1 h2
  refine (norm_add_le _ _).trans ?_
  rw [h3]
  linarith [norm_add_le ((x.2.2.1 ⊗ₖ v.2.2.2.1) * insertResource (Fin d) (Fin d) x.1)
    ((v.2.2.1 ⊗ₖ x.2.2.2.1) * insertResource (Fin d) (Fin d) x.1)]

theorem IsValid.frobNorm_reverseVelocity_le {x : PVMReverseBlocks s} (hx : IsValid x)
    (v : PVMReverseBlocks s) :
    ‖reverseVelocity x v‖ ≤ ‖v.2.2.2.2.2‖ + ‖v.2.2.2.2.1‖ +
      Real.sqrt (∑ i, ‖WithLp.toLp 2 (v.2.1 i)‖ ^ 2) := by
  rw [reverseVelocity, Matrix.add_mul]
  have h1 := frobNorm_kronecker_isometry_left_mul_compressedFlag_le v.2.2.2.2.2 hx.2.2.2.2.1 hx.2.1
  have h2 := frobNorm_kronecker_isometry_right_mul_compressedFlag_le v.2.2.2.2.1 hx.2.2.2.2.2 hx.2.1
  have h3 : ‖(x.2.2.2.2.1 ⊗ₖ x.2.2.2.2.2) * compressedFlag v.2.1‖ =
      Real.sqrt (∑ i, ‖WithLp.toLp 2 (v.2.1 i)‖ ^ 2) := by
    rw [(hx.2.2.2.2.1.kronecker hx.2.2.2.2.2).frobNorm_mul_eq, ← frobNorm_compressedFlag_sq,
      Real.sqrt_sq (norm_nonneg _)]
  refine (norm_add_le _ _).trans ?_
  rw [h3]
  linarith [norm_add_le ((x.2.2.2.2.1 ⊗ₖ v.2.2.2.2.2) * compressedFlag x.2.1)
    ((v.2.2.2.2.1 ⊗ₖ x.2.2.2.2.2) * compressedFlag x.2.1)]

/-- Frobenius speed in the normalized block coordinates. -/
theorem IsValid.frobNorm_velocities_rescaled_le {x : PVMReverseBlocks s} (hx : IsValid x)
    (v : PVMReverseBlocks s) :
    ‖forwardVelocity x (rescaleBlocks v)‖ + ‖reverseVelocity x (rescaleBlocks v)‖ ≤
      Real.sqrt (2 * (d : ℝ) ^ 2 + 2 * ((d : ℝ) ^ 2 * s.1.r) + 2 * s.supportSize) *
        euclideanNorm v := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hkr : Real.sqrt d * Real.sqrt (d * s.1.r) = d * Real.sqrt s.1.r := by
    rw [Real.sqrt_mul hd0, ← mul_assoc, Real.mul_self_sqrt hd0]
  have hf := hx.frobNorm_forwardVelocity_le (rescaleBlocks v)
  have hr := hx.frobNorm_reverseVelocity_le (rescaleBlocks v)
  change _ ≤ Real.sqrt d * ‖Real.sqrt (d * s.1.r : ℝ) • v.2.2.2.1‖ +
    Real.sqrt d * ‖Real.sqrt (d * s.1.r : ℝ) • v.2.2.1‖ + d * ‖WithLp.toLp 2 v.1‖ at hf
  change _ ≤ ‖Real.sqrt (s.supportSize : ℝ) • v.2.2.2.2.2‖ +
    ‖Real.sqrt (s.supportSize : ℝ) • v.2.2.2.2.1‖ +
    Real.sqrt (∑ i, ‖WithLp.toLp 2 ((Real.sqrt (d ^ 2 : ℝ) • v.2.1) i)‖ ^ 2) at hr
  rw [garbageNorm_smul] at hr
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hf hr
  rw [Real.sqrt_sq hd0] at hr
  rw [← mul_assoc, ← mul_assoc, hkr] at hf
  let weights : Fin 6 → ℝ := ![d, d, d * Real.sqrt s.1.r, d * Real.sqrt s.1.r,
    Real.sqrt s.supportSize, Real.sqrt s.supportSize]
  have hsum : ∑ i, weights i * blockNorms v i =
      d * ‖WithLp.toLp 2 v.1‖ + d * Real.sqrt (∑ i, ‖WithLp.toLp 2 (v.2.1 i)‖ ^ 2) +
        d * Real.sqrt s.1.r * ‖v.2.2.1‖ + d * Real.sqrt s.1.r * ‖v.2.2.2.1‖ +
        Real.sqrt s.supportSize * ‖v.2.2.2.2.1‖ + Real.sqrt s.supportSize * ‖v.2.2.2.2.2‖ := by
    simp [weights, blockNorms, Fin.sum_univ_succ]
    ring
  have hw : ∑ i, weights i ^ 2 =
      2 * (d : ℝ) ^ 2 + 2 * ((d : ℝ) ^ 2 * s.1.r) + 2 * s.supportSize := by
    simp [weights, Fin.sum_univ_succ, mul_pow, Real.sq_sqrt (Nat.cast_nonneg s.1.r),
      Real.sq_sqrt (Nat.cast_nonneg s.supportSize)]
    ring
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ weights (blockNorms v)
  rw [hw] at hcs
  have hmain : ‖forwardVelocity x (rescaleBlocks v)‖ + ‖reverseVelocity x (rescaleBlocks v)‖ ≤
      ∑ i, weights i * blockNorms v i := by
    rw [hsum]
    linarith
  exact hmain.trans hcs

/-- For near-Bell shapes with `d³ ≤ 2K` the speed coefficient is at most `4√K`. -/
theorem nearBell_speedConstant_le {s : PVMReverseShape d K} (hs : s.IsNearBell) (hd : 2 ≤ d)
    (hd3 : (d : ℝ) ^ 3 ≤ 2 * K) :
    Real.sqrt (2 * (d : ℝ) ^ 2 + 2 * ((d : ℝ) ^ 2 * s.1.r) + 2 * s.supportSize) ≤
      4 * Real.sqrt K := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hr := hs.resource_le
  have hS := hs.supportSize_le hd hd3
  have hS' : (s.supportSize : ℝ) ≤ 2 * K := by nlinarith [Nat.cast_nonneg (α := ℝ) s.supportSize]
  have hd2 : 2 * (d : ℝ) ^ 2 ≤ 2 * K := by nlinarith
  have htot : 2 * (d : ℝ) ^ 2 + 2 * ((d : ℝ) ^ 2 * s.1.r) + 2 * s.supportSize ≤ 16 * K := by
    nlinarith [Nat.cast_nonneg (α := ℝ) K]
  calc _ ≤ Real.sqrt (16 * K) := Real.sqrt_le_sqrt htot
    _ = 4 * Real.sqrt K := by
        rw [Real.sqrt_mul (by norm_num), show (16 : ℝ) = 4 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]

/-- **`lem:bell-cutoff`, block form.** For a near-Bell shape with `d³ ≤ 2K`, at a valid
normalized witness with leakage `h ≤ d²δ²`: `dT̂ = T + R` with
`rank T ≤ 4d² − 3 + 4d²⌊d²/64⌋`, `‖dT̂(v)‖ ≤ 4√K‖v‖` and `‖R v‖ ≤ 32δ√K‖v‖`. -/
theorem exists_extendedOverlap_sharp_decomposition {x : PVMReverseBlocks s}
    (hs : s.IsNearBell) (hx : IsValid (rescaleBlocks x)) (hd : 2 ≤ d)
    (hd3 : (d : ℝ) ^ 3 ≤ 2 * K) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdef : (d : ℝ) ^ 2 - ‖overlap (rescaleBlocks x)‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2) :
    ∃ T R : PVMReverseBlocks s →ₗ[ℝ] Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      (fderiv ℝ extendedOverlap x).toLinearMap = T + R ∧
      Module.finrank ℝ (LinearMap.range T) ≤ strongUncontrolledRank d ∧
      (∀ v, ‖fderiv ℝ extendedOverlap x v‖ ≤ 4 * Real.sqrt K * euclideanNorm v) ∧
      (∀ v, ‖R v‖ ≤ 32 * δ * Real.sqrt K * euclideanNorm v) := by
  have hd0 : 0 < d := by omega
  have hA := hx.isIsometry_forward
  have hB := hx.isIsometry_reverse
  have hres := crossGram_residuals_sq (forward (rescaleBlocks x)) (reverse (rescaleBlocks x)) hA hB
  have hD : (Fintype.card (Fin d × Fin d) : ℝ) = (d : ℝ) ^ 2 := by simp [pow_two]
  obtain ⟨RA, hRA⟩ : ∃ RA, RA = forward (rescaleBlocks x) - reverse (rescaleBlocks x) *
      ((reverse (rescaleBlocks x))ᴴ * forward (rescaleBlocks x)) := ⟨_, rfl⟩
  obtain ⟨RB, hRB⟩ : ∃ RB, RB = reverse (rescaleBlocks x) - forward (rescaleBlocks x) *
      ((reverse (rescaleBlocks x))ᴴ * forward (rescaleBlocks x))ᴴ := ⟨_, rfl⟩
  have hRA2 : ‖RA‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2 := by rw [hRA, hres.1, hD]; exact hdef
  have hRB2 : ‖RB‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2 := by rw [hRB, hres.2, hD]; exact hdef
  have hc : (0 : ℝ) < if 0 < δ then 8 * δ else 1 := by
    split_ifs with h
    · positivity
    · norm_num
  obtain ⟨UA, SA, _, _, hSA, hgA⟩ := exists_spectral_cutoff RA hc
  obtain ⟨UB, SB, _, _, hSB, hgB⟩ := exists_spectral_cutoff RB hc
  have hSAn : 64 * SA.card ≤ d ^ 2 := spectralCutoff_card_le hδ hSA hRA2
  have hSBn : 64 * SB.card ≤ d ^ 2 := spectralCutoff_card_le hδ hSB hRB2
  have hgA' : opNorm (RA * (1 - cutoffProjection UA SA)) ≤ 8 * δ := spectralCutoff_good_le hδ hgA hRA2
  have hgB' : opNorm (RB * (1 - cutoffProjection UB SB)) ≤ 8 * δ := spectralCutoff_good_le hδ hgB hRB2
  let PA := cutoffProjection UA SA
  let PB := cutoffProjection UB SB
  let L := (rescaleBlocks (s := s)).comp (fderiv ℝ normalizedCubicBlocks x).toLinearMap
  let Af := (fderiv ℝ forward (rescaleBlocks x)).toLinearMap.comp L
  let Bf := (fderiv ℝ reverse (rescaleBlocks x)).toLinearMap.comp L
  let bad : PVMReverseBlocks s →ₗ[ℝ] Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
    (mulRightReal (k := Fin d × Fin d) PA).comp ((adjointMulReal RA).comp Bf) +
      (mulLeftReal (k := Fin d × Fin d) PB).comp ((mulLeftRectReal RBᴴ).comp Af)
  have hAf : ∀ v, Af v = forwardVelocity (rescaleBlocks x)
      (rescaleBlocks (fderiv ℝ normalizedCubicBlocks x v)) := fun v =>
    fderiv_forward_apply (rescaleBlocks x) _
  have hBf : ∀ v, Bf v = reverseVelocity (rescaleBlocks x)
      (rescaleBlocks (fderiv ℝ normalizedCubicBlocks x v)) := fun v =>
    fderiv_reverse_apply (rescaleBlocks x) _
  have hspeed : ∀ v, ‖Af v‖ + ‖Bf v‖ ≤ 4 * Real.sqrt K * euclideanNorm v := fun v => by
    rw [hAf, hBf]
    refine (hx.frobNorm_velocities_rescaled_le _).trans ?_
    exact mul_le_mul (nearBell_speedConstant_le hs hd hd3)
      (euclideanNorm_fderiv_normalizedCubicBlocks_le hx hd0 v) (euclideanNorm_nonneg _)
      (by positivity)
  refine ⟨extendedLocalTerm x + bad, extendedResidual x - bad, ?_, ?_, ?_, ?_⟩
  · rw [fderiv_extendedOverlap_decomposition]
    abel
  · have hloc := finrank_extendedLocalTerm_le hx hd0
    have hbadA : Module.finrank ℝ (LinearMap.range
        ((mulRightReal (k := Fin d × Fin d) PA).comp ((adjointMulReal RA).comp Bf))) ≤
        2 * d ^ 2 * SA.card := by
      have h := finrank_range_mulRight_cutoffProjection_le (k := Fin d × Fin d) UA SA
      simp only [Fintype.card_prod, Fintype.card_fin] at h
      exact (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)).trans
        (by simpa [pow_two] using h)
    have hbadB : Module.finrank ℝ (LinearMap.range
        ((mulLeftReal (k := Fin d × Fin d) PB).comp ((mulLeftRectReal RBᴴ).comp Af))) ≤
        2 * d ^ 2 * SB.card := by
      have h := finrank_range_mulLeft_cutoffProjection_le (k := Fin d × Fin d) UB SB
      simp only [Fintype.card_prod, Fintype.card_fin] at h
      exact (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)).trans
        (by simpa [pow_two] using h)
    have hbad : Module.finrank ℝ (LinearMap.range bad) ≤
        2 * d ^ 2 * SA.card + 2 * d ^ 2 * SB.card :=
      (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
        ((Submodule.finrank_add_le_finrank_add_finrank _ _).trans (add_le_add hbadA hbadB))
    have hsum := (Submodule.finrank_mono (LinearMap.range_add_le (extendedLocalTerm x) bad)).trans
      ((Submodule.finrank_add_le_finrank_add_finrank _ _).trans (add_le_add hloc hbad))
    have hA64 : SA.card ≤ d ^ 2 / 64 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by linarith)
    have hB64 : SB.card ≤ d ^ 2 / 64 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by linarith)
    have h1 := Nat.mul_le_mul_left (2 * d ^ 2) hA64
    have h2 := Nat.mul_le_mul_left (2 * d ^ 2) hB64
    have h12 : 2 * d ^ 2 * SA.card + 2 * d ^ 2 * SB.card ≤ 4 * d ^ 2 * (d ^ 2 / 64) :=
      (add_le_add h1 h2).trans_eq (by ring)
    have hd1 : 1 ≤ d ^ 2 := Nat.one_le_pow _ _ hd0
    have hloc' : 3 * d ^ 2 - 2 ≤ 4 * d ^ 2 - 3 := by omega
    unfold strongUncontrolledRank
    exact hsum.trans (add_le_add hloc' h12)
  · intro v
    rw [fderiv_extendedOverlap_apply hx hd0, overlapVelocity]
    refine (frobNorm_crossGramVelocity_le hA hB _ _).trans ?_
    rw [← hAf v, ← hBf v]
    exact hspeed v
  · intro v
    have hrv : extendedResidual x v = crossGramResidual (forward (rescaleBlocks x))
        (reverse (rescaleBlocks x)) (Af v) (Bf v) := by
      rw [hAf, hBf]
      exact extendedResidual_apply hx hd0 v
    have heq : (extendedResidual x - bad) v =
        (Bf v)ᴴ * (RA * (1 - PA)) + (RB * (1 - PB))ᴴ * Af v := by
      rw [LinearMap.sub_apply, hrv, crossGramResidual_eq_leakage, ← hRA, ← hRB]
      exact leakage_sub_cutoff (Af v) (Bf v) RA RB PA PB
        (conjTranspose_cutoffProjection UB SB)
    rw [heq]
    have h1 : ‖(Bf v)ᴴ * (RA * (1 - PA))‖ ≤ 8 * δ * ‖Bf v‖ := by
      refine (frobNorm_mul_le' _ _).trans ?_
      rw [Matrix.frobenius_norm_conjTranspose]
      nlinarith [norm_nonneg (Bf v)]
    have h2 : ‖(RB * (1 - PB))ᴴ * Af v‖ ≤ 8 * δ * ‖Af v‖ := by
      refine (frobNorm_mul_le _ _).trans ?_
      rw [opNorm_conjTranspose]
      nlinarith [norm_nonneg (Af v)]
    have hsp := hspeed v
    have hδ8 : 0 ≤ 8 * δ := by positivity
    calc _ ≤ ‖(Bf v)ᴴ * (RA * (1 - PA))‖ + ‖(RB * (1 - PB))ᴴ * Af v‖ := norm_add_le _ _
      _ ≤ 8 * δ * (‖Af v‖ + ‖Bf v‖) := by linarith
      _ ≤ 8 * δ * (4 * Real.sqrt K * euclideanNorm v) := mul_le_mul_of_nonneg_left hsp hδ8
      _ = _ := by ring

variable (s) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) {P : ℕ} (hP : PVMReverseShape.AdmissibleBudget s P)

/-- **`lem:bell-cutoff`.** On the polynomial witness source of a near-Bell shape with
`d³ ≤ 2K`, the ambient derivative of the overlap map (in Frobenius output coordinates) splits as
`T + R` with `rank T ≤ ℓ⋆ = 4d² − 3 + 4d²⌊d²/64⌋`, `‖dT̂‖ ≤ 4√K` and `‖R‖ ≤ 32δ√K`; in the
normalized norm these are `4√(K/d²)` and `32δ√(K/d²)`. -/
theorem witnessFormat_nearBell_rank_error (hs : s.IsNearBell) (hd2 : 2 ≤ d)
    (hd3 : (d : ℝ) ^ 3 ≤ 2 * K) {δ : ℝ} (hδ : 0 ≤ δ)
    {x : RealEuclidean P} (hx : x ∈ (witnessFormat s hd hfloor hP δ).source) :
    ∃ T R : RealEuclidean P →L[ℝ] RealEuclidean (2 * d ^ 4),
      fderiv ℝ (coordinateOverlapPolynomial s hd hfloor hP).eval x = T + R ∧
      Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ strongUncontrolledRank d ∧
      ‖fderiv ℝ (coordinateOverlapPolynomial s hd hfloor hP).eval x‖ ≤ 4 * Real.sqrt K ∧
      ‖R‖ ≤ 32 * δ * Real.sqrt K := by
  obtain ⟨hv, _, hdef⟩ := (mem_witnessFormat_source_iff s hd hfloor hP δ x).mp hx
  obtain ⟨T0, R0, hdec, hrank, hnorm, hR⟩ :=
    exists_extendedOverlap_sharp_decomposition hs hv hd2 hd3 hδ hdef
  have he : (coordinateOverlapPolynomial s hd hfloor hP).eval = coordinateOverlap s hd hfloor hP :=
    funext (coordinateOverlapPolynomial_eval s hd hfloor hP)
  rw [he]
  let O := (overlapOutputCoordinates d).toLinearMap
  let D := decodeCoordinates s hd hfloor hP
  let T := (O.comp (T0.comp D)).toContinuousLinearMap
  let R := (O.comp (R0.comp D)).toContinuousLinearMap
  refine ⟨T, R, ?_, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro v
    rw [fderiv_coordinateOverlap_apply]
    have h := congrArg (fun L => L (D v)) hdec
    simp only [ContinuousLinearMap.coe_coe, LinearMap.add_apply] at h
    rw [h, map_add]
    rfl
  · change Module.finrank ℝ (LinearMap.range (O.comp (T0.comp D))) ≤ _
    rw [LinearMap.range_comp]
    exact (Submodule.finrank_map_le _ _).trans
      ((Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)).trans hrank)
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [fderiv_coordinateOverlap_apply, norm_overlapOutputCoordinates]
    calc _ ≤ 4 * Real.sqrt K * euclideanNorm (D v) := hnorm _
      _ ≤ 4 * Real.sqrt K * ‖v‖ :=
          mul_le_mul_of_nonneg_left (euclideanNorm_decodeCoordinates_le s hd hfloor hP v)
            (by positivity)
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    change ‖overlapOutputCoordinates d (R0 (D v))‖ ≤ _
    rw [norm_overlapOutputCoordinates]
    calc _ ≤ 32 * δ * Real.sqrt K * euclideanNorm (D v) := hR _
      _ ≤ 32 * δ * Real.sqrt K * ‖v‖ :=
          mul_le_mul_of_nonneg_left (euclideanNorm_decodeCoordinates_le s hd hfloor hP v)
            (by positivity)

end PVMReverseBlocks

end NLQCLean

import NLQCLean.Approx.SlimPolynomialWitness
import NLQCLean.LinearAlgebra.ResidualSpectralCutoff
import NLQCLean.LinearAlgebra.FrobeniusInsertion

/-!
# Sharp velocity bounds and the rank/error split of the slim witness

At every point of the slim polynomial source:

* the Frobenius velocities obey `‖A'‖ + ‖B'‖ ≤ d √(2r + 2s + 2) ‖v‖ ≤ 4 √K ‖v‖`, using the
  tensor-insertion identity rather than an operator-to-Frobenius conversion;
* both leakage residuals `R_A = A − B BᴴA`, `R_B = B − A (BᴴA)ᴴ` are split at `8δ`: the bad
  parts have rank at most `⌊D/64⌋` and contribute at most `4D⌊D/64⌋` real directions;
* the normalized output derivative is `T + R` with `rank T ≤ strongUncontrolledRank d`,
  `‖dh‖ ≤ 4√K/d` and `‖R‖ ≤ 32 δ √K/d`.

The cutoffs are chosen pointwise; no smooth or polynomial choice of them is claimed.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

/-- Real-linear `M ↦ Mᴴ * C`. -/
def adjointMulReal {k l n : Type*} [Fintype l] (C : Matrix l n ℂ) :
    Matrix l k ℂ →ₗ[ℝ] Matrix k n ℂ where
  toFun M := Mᴴ * C
  map_add' M N := by rw [Matrix.conjTranspose_add, Matrix.add_mul]
  map_smul' c M := by
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul]
    rfl

/-- Real-linear `M ↦ C * M` for rectangular matrices. -/
def mulLeftRectReal {k l n : Type*} [Fintype l] (C : Matrix k l ℂ) :
    Matrix l n ℂ →ₗ[ℝ] Matrix k n ℂ where
  toFun M := C * M
  map_add' M N := Matrix.mul_add C M N
  map_smul' c M := Matrix.mul_smul C c M

theorem frobNorm_crossGramVelocity_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {A B : Matrix m n ℂ} (hA : IsIsometry A) (hB : IsIsometry B)
    (A' B' : Matrix m n ℂ) : ‖crossGramVelocity A B A' B'‖ ≤ ‖A'‖ + ‖B'‖ := by
  rw [crossGramVelocity]
  have h1 : ‖B'ᴴ * A‖ ≤ ‖B'‖ := (frobNorm_mul_le' _ _).trans (by
    rw [Matrix.frobenius_norm_conjTranspose]
    simpa using mul_le_mul_of_nonneg_left hA.opNorm_le_one (norm_nonneg B'))
  have h2 : ‖Bᴴ * A'‖ ≤ ‖A'‖ := (frobNorm_mul_le _ _).trans (by
    rw [opNorm_conjTranspose]
    simpa using mul_le_mul_of_nonneg_right hB.opNorm_le_one (norm_nonneg A'))
  linarith [norm_add_le (B'ᴴ * A) (Bᴴ * A')]

/-- The pointwise cutoff level `8δ` (or `1` when `δ = 0`). -/
theorem spectralCutoff_card_le {d S : ℕ} {δ R : ℝ} (hδ : 0 ≤ δ)
    (h1 : (S : ℝ) * (if 0 < δ then 8 * δ else 1) ^ 2 ≤ R) (h2 : R ≤ (d : ℝ) ^ 2 * δ ^ 2) :
    64 * S ≤ d ^ 2 := by
  rcases hδ.lt_or_eq with hpos | h0
  · rw [ite_eq_left hpos] at h1
    have hδ2 : 0 < δ ^ 2 := by positivity
    have h3 : (64 * S : ℝ) * δ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2 := by nlinarith
    exact_mod_cast le_of_mul_le_mul_right h3 hδ2
  · subst h0
    rw [ite_eq_right (lt_irrefl 0), one_pow, mul_one] at h1
    have h2' : R ≤ 0 := by simpa using h2
    have hS0 : (S : ℝ) ≤ 0 := h1.trans h2'
    have : S = 0 := by exact_mod_cast le_antisymm hS0 (Nat.cast_nonneg S)
    simp [this]

theorem spectralCutoff_good_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {d : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) {R : Matrix m n ℂ} {P : Matrix n n ℂ}
    (h1 : opNorm (R * (1 - P)) ≤ if 0 < δ then 8 * δ else 1)
    (h2 : ‖R‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2) : opNorm (R * (1 - P)) ≤ 8 * δ := by
  rcases hδ.lt_or_eq with hpos | h0
  · rwa [ite_eq_left hpos] at h1
  · subst h0
    have h2' : ‖R‖ ^ 2 ≤ 0 := by simpa using h2
    have hR : R = 0 := norm_eq_zero.mp (le_antisymm (by nlinarith [norm_nonneg R]) (norm_nonneg R))
    rw [hR, Matrix.zero_mul]
    exact (opNorm_le_frobNorm _).trans (by simp)

/-- Removing the two bad cutoff pieces from the leakage form of the residual. -/
theorem leakage_sub_cutoff {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A' B' : Matrix m n ℂ) (RA : Matrix m n ℂ) (RB : Matrix m n ℂ) (PA PB : Matrix n n ℂ)
    (hPB : PBᴴ = PB) :
    (B'ᴴ * RA + RBᴴ * A') - (B'ᴴ * RA * PA + PB * (RBᴴ * A')) =
      B'ᴴ * (RA * (1 - PA)) + (RB * (1 - PB))ᴴ * A' := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPB]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  abel

namespace SlimReverseBlocks

variable {d K : ℕ} {s : SlimReverseShape d K}

theorem IsValid.frobNorm_forwardVelocity_le {x : SlimReverseBlocks s} (hx : IsValid x)
    (v : SlimReverseBlocks s) :
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

theorem IsValid.frobNorm_reverseVelocity_le {x : SlimReverseBlocks s} (hx : IsValid x)
    (v : SlimReverseBlocks s) :
    ‖reverseVelocity x v‖ ≤
      Real.sqrt d * ‖v.2.2.2.2.2‖ + Real.sqrt d * ‖v.2.2.2.2.1‖ + d * ‖WithLp.toLp 2 v.2.1‖ := by
  rw [reverseVelocity, tensorInsertionVelocity, Matrix.add_mul]
  have h1 := frobNorm_kronecker_isometry_left_mul_insertResource_le (a := Fin d) (b := Fin d)
    hx.2.2.2.2.1 v.2.2.2.2.2 hx.2.1
  have h2 := frobNorm_kronecker_isometry_right_mul_insertResource_le (a := Fin d) (b := Fin d)
    v.2.2.2.2.1 hx.2.2.2.2.2 hx.2.1
  have h3 : ‖(x.2.2.2.2.1 ⊗ₖ x.2.2.2.2.2) * insertResource (Fin d) (Fin d) v.2.1‖ =
      d * ‖WithLp.toLp 2 v.2.1‖ := by
    rw [(hx.2.2.2.2.1.kronecker hx.2.2.2.2.2).frobNorm_mul_eq, norm_insertResource]
    simp [Fintype.card_prod, Fintype.card_fin, Real.sqrt_mul_self (Nat.cast_nonneg d)]
  simp only [Fintype.card_fin] at h1 h2
  refine (norm_add_le _ _).trans ?_
  rw [h3]
  linarith [norm_add_le ((x.2.2.2.2.1 ⊗ₖ v.2.2.2.2.2) * insertResource (Fin d) (Fin d) x.2.1)
    ((v.2.2.2.2.1 ⊗ₖ x.2.2.2.2.2) * insertResource (Fin d) (Fin d) x.2.1)]

/-- Sharp Frobenius speed in the normalized block coordinates. -/
theorem IsValid.frobNorm_velocities_rescaled_le {x : SlimReverseBlocks s} (hx : IsValid x)
    (v : SlimReverseBlocks s) :
    ‖forwardVelocity x (rescaleBlocks v)‖ + ‖reverseVelocity x (rescaleBlocks v)‖ ≤
      d * Real.sqrt (2 * s.1.r + 2 * frozenSupport d K + 2) * euclideanNorm v := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hkr : Real.sqrt d * Real.sqrt (d * s.1.r) = d * Real.sqrt s.1.r := by
    rw [Real.sqrt_mul hd0, ← mul_assoc, Real.mul_self_sqrt hd0]
  have hks : Real.sqrt d * Real.sqrt (d * frozenSupport d K) = d * Real.sqrt (frozenSupport d K) := by
    rw [Real.sqrt_mul hd0, ← mul_assoc, Real.mul_self_sqrt hd0]
  have hnA : ‖(rescaleBlocks v).2.2.1‖ = Real.sqrt (d * s.1.r) * ‖v.2.2.1‖ := by
    simp [rescaleBlocks, norm_smul, abs_of_nonneg, Real.sqrt_nonneg]
  have hnB : ‖(rescaleBlocks v).2.2.2.1‖ = Real.sqrt (d * s.1.r) * ‖v.2.2.2.1‖ := by
    simp [rescaleBlocks, norm_smul, abs_of_nonneg, Real.sqrt_nonneg]
  have hnTA : ‖(rescaleBlocks v).2.2.2.2.1‖ = Real.sqrt (d * frozenSupport d K) * ‖v.2.2.2.2.1‖ := by
    simp [rescaleBlocks, norm_smul, abs_of_nonneg, Real.sqrt_nonneg]
  have hnTB : ‖(rescaleBlocks v).2.2.2.2.2‖ = Real.sqrt (d * frozenSupport d K) * ‖v.2.2.2.2.2‖ := by
    simp [rescaleBlocks, norm_smul, abs_of_nonneg, Real.sqrt_nonneg]
  have hf := hx.frobNorm_forwardVelocity_le (rescaleBlocks v)
  have hr := hx.frobNorm_reverseVelocity_le (rescaleBlocks v)
  rw [hnA, hnB, ← mul_assoc, ← mul_assoc, hkr] at hf
  rw [hnTA, hnTB, ← mul_assoc, ← mul_assoc, hks] at hr
  change ‖forwardVelocity x (rescaleBlocks v)‖ ≤ _ + _ + (d : ℝ) * ‖WithLp.toLp 2 v.1‖ at hf
  change ‖reverseVelocity x (rescaleBlocks v)‖ ≤ _ + _ + (d : ℝ) * ‖WithLp.toLp 2 v.2.1‖ at hr
  let weights : Fin 6 → ℝ := ![1, 1, Real.sqrt s.1.r, Real.sqrt s.1.r,
    Real.sqrt (frozenSupport d K), Real.sqrt (frozenSupport d K)]
  have hsum : ∑ i, weights i * blockNorms v i =
      ‖WithLp.toLp 2 v.1‖ + ‖WithLp.toLp 2 v.2.1‖ + Real.sqrt s.1.r * ‖v.2.2.1‖ +
        Real.sqrt s.1.r * ‖v.2.2.2.1‖ + Real.sqrt (frozenSupport d K) * ‖v.2.2.2.2.1‖ +
        Real.sqrt (frozenSupport d K) * ‖v.2.2.2.2.2‖ := by
    simp [weights, blockNorms, Fin.sum_univ_succ]
    ring
  have hw : ∑ i, weights i ^ 2 = 2 * (s.1.r : ℝ) + 2 * frozenSupport d K + 2 := by
    simp [weights, Fin.sum_univ_succ, Real.sq_sqrt (Nat.cast_nonneg s.1.r),
      Real.sq_sqrt (Nat.cast_nonneg (frozenSupport d K))]
    ring
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ weights (blockNorms v)
  rw [hw] at hcs
  have hmain : ‖forwardVelocity x (rescaleBlocks v)‖ + ‖reverseVelocity x (rescaleBlocks v)‖ ≤
      d * ∑ i, weights i * blockNorms v i := by
    rw [hsum]
    nlinarith
  calc _ ≤ d * ∑ i, weights i * blockNorms v i := hmain
    _ ≤ d * (Real.sqrt (2 * (s.1.r : ℝ) + 2 * frozenSupport d K + 2) *
          Real.sqrt (∑ i, blockNorms v i ^ 2)) := mul_le_mul_of_nonneg_left hcs hd0
    _ = _ := by rw [euclideanNorm]; ring

/-- The slim speed constant is at most `4 √K`. -/
theorem slim_speedConstant_le (s : SlimReverseShape d K) (hd : 2 ≤ d) :
    (d : ℝ) * Real.sqrt (2 * s.1.r + 2 * frozenSupport d K + 2) ≤ 4 * Real.sqrt K := by
  have hK2 := SlimReverseShape.sq_le_two_mul_budget s
  have hfs := sq_mul_frozenSupport_le (by omega : 0 < d) hK2
  have hrN : d ^ 2 * s.1.r ≤ 2 * K := by
    calc d ^ 2 * s.1.r ≤ 2 * (s.1.mA * s.1.mB) * s.1.r :=
          Nat.mul_le_mul_right _ (SlimReverseShape.sq_le_two_mul_messages s)
      _ = 2 * (s.1.r * s.1.mA * s.1.mB) := by ring
      _ ≤ 2 * K := Nat.mul_le_mul_left 2 s.1.footprint
  have htot : d ^ 2 * (2 * s.1.r + 2 * frozenSupport d K + 2) ≤ 16 * K := by nlinarith
  have htotR : (d : ℝ) ^ 2 * (2 * s.1.r + 2 * frozenSupport d K + 2) ≤ 16 * K := by
    exact_mod_cast htot
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [show (d : ℝ) = Real.sqrt ((d : ℝ) ^ 2) from (Real.sqrt_sq hd0).symm,
    ← Real.sqrt_mul (sq_nonneg _)]
  calc Real.sqrt ((d : ℝ) ^ 2 * (2 * s.1.r + 2 * frozenSupport d K + 2)) ≤ Real.sqrt (16 * K) :=
        Real.sqrt_le_sqrt htotR
    _ = 4 * Real.sqrt K := by
        rw [Real.sqrt_mul (by norm_num), show (16 : ℝ) = 4 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]

theorem IsValid.frobNorm_velocities_rescaled_le_sqrt {x : SlimReverseBlocks s} (hx : IsValid x)
    (hd : 2 ≤ d) (v : SlimReverseBlocks s) :
    ‖forwardVelocity x (rescaleBlocks v)‖ + ‖reverseVelocity x (rescaleBlocks v)‖ ≤
      4 * Real.sqrt K * euclideanNorm v :=
  (hx.frobNorm_velocities_rescaled_le v).trans
    (mul_le_mul_of_nonneg_right (slim_speedConstant_le s hd) (euclideanNorm_nonneg v))

/-- On the slim block space: `dH = T + R`, `rank T ≤ b`, `‖dH‖ ≤ 4√K`, `‖R‖ ≤ 32 δ √K`. -/
theorem exists_extendedOverlap_sharp_decomposition {x : SlimReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdef : (d : ℝ) ^ 2 - ‖overlap (rescaleBlocks x)‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2) :
    ∃ T R : SlimReverseBlocks s →ₗ[ℝ] Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
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
  let bad : SlimReverseBlocks s →ₗ[ℝ] Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
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
    exact (hx.frobNorm_velocities_rescaled_le_sqrt hd _).trans
      (mul_le_mul_of_nonneg_left (euclideanNorm_fderiv_normalizedCubicBlocks_le hx hd0 v)
        (by positivity))
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
    exact hsum.trans (Nat.add_le_add_left h12 _)
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

variable (s) (hd : 2 ≤ d)

/-- Ambient derivative bound: the normalized polynomial derivative at every source point. -/
theorem witnessFormat_sharp_rank_error {δ : ℝ} (hδ : 0 ≤ δ)
    {x : RealEuclidean (slimCoordinateBudget K)} (hx : x ∈ (witnessFormat s hd δ).source) :
    ∃ T R : RealEuclidean (slimCoordinateBudget K) →L[ℝ] RealEuclidean (2 * d ^ 4),
      fderiv ℝ (coordinateOverlapPolynomial s hd).eval x = T + R ∧
      Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ strongUncontrolledRank d ∧
      ‖fderiv ℝ (coordinateOverlapPolynomial s hd).eval x‖ ≤ 4 * Real.sqrt K / d ∧
      ‖R‖ ≤ 32 * δ * Real.sqrt K / d := by
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  obtain ⟨hv, _, hdef⟩ := (mem_witnessFormat_source_iff s hd δ x).mp hx
  obtain ⟨T0, R0, hdec, hrank, hnorm, hR⟩ :=
    exists_extendedOverlap_sharp_decomposition hv hd hδ hdef
  have he : (coordinateOverlapPolynomial s hd).eval = coordinateOverlap s hd :=
    funext (coordinateOverlapPolynomial_eval s hd)
  rw [he]
  let T := ((normalizedOutputCoordinates d).comp (T0.comp (decodeCoordinates s hd))).toContinuousLinearMap
  let R := ((normalizedOutputCoordinates d).comp (R0.comp (decodeCoordinates s hd))).toContinuousLinearMap
  refine ⟨T, R, ?_, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro v
    rw [fderiv_coordinateOverlap_apply]
    have h := congrArg (fun L => L (decodeCoordinates s hd v)) hdec
    simp only [ContinuousLinearMap.coe_coe, LinearMap.add_apply] at h
    rw [h, map_add]
    rfl
  · change Module.finrank ℝ (LinearMap.range ((normalizedOutputCoordinates d).comp
      (T0.comp (decodeCoordinates s hd)))) ≤ _
    rw [LinearMap.range_comp]
    exact (Submodule.finrank_map_le _ _).trans
      ((Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)).trans hrank)
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [fderiv_coordinateOverlap_apply, norm_normalizedOutputCoordinates hd0, div_le_iff₀ hdR]
    calc _ ≤ 4 * Real.sqrt K * euclideanNorm (decodeCoordinates s hd v) := hnorm _
      _ ≤ 4 * Real.sqrt K * ‖v‖ :=
          mul_le_mul_of_nonneg_left (euclideanNorm_decodeCoordinates_le s hd v) (by positivity)
      _ = _ := by field_simp
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    change ‖normalizedOutputCoordinates d (R0 (decodeCoordinates s hd v))‖ ≤ _
    rw [norm_normalizedOutputCoordinates hd0, div_le_iff₀ hdR]
    calc _ ≤ 32 * δ * Real.sqrt K * euclideanNorm (decodeCoordinates s hd v) := hR _
      _ ≤ 32 * δ * Real.sqrt K * ‖v‖ :=
          mul_le_mul_of_nonneg_left (euclideanNorm_decodeCoordinates_le s hd v) (by positivity)
      _ = _ := by field_simp

end SlimReverseBlocks
end NLQCLean

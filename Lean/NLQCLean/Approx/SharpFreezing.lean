import NLQCLean.Approx.ChoiProjection

/-!
# Sharp bounded-rank freezing

Normalize the proved Choi projection, truncate only its
Schmidt rank, and retain the positive overlap to obtain the sharp constant.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

/-- Normalize a nonzero coefficient matrix, recording both the unit norm
and the phase of its overlap with the original matrix. -/
theorem exists_normalized_matrix {m n : Type*} [Fintype m] [Fintype n]
    (Z : Matrix m n ℂ) (hZ : 0 < ‖Z‖) :
    ∃ Γ : Matrix m n ℂ, ‖Γ‖ = 1 ∧ Z = (‖Z‖ : ℂ) • Γ ∧
      frobInner Γ Z = (‖Z‖ : ℂ) := by
  let Γ : Matrix m n ℂ := ((‖Z‖ : ℂ)⁻¹) • Z
  have hn : (‖Z‖ : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  refine ⟨Γ, ?_, ?_, ?_⟩
  · change ‖((‖Z‖ : ℂ)⁻¹) • Z‖ = 1
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hZ.le, inv_mul_cancel₀ hZ.ne']
  · change Z = (‖Z‖ : ℂ) • (((‖Z‖ : ℂ)⁻¹) • Z)
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  · change frobInner (((‖Z‖ : ℂ)⁻¹) • Z) Z = _
    rw [frobInner_smul_left, frobInner_self_eq_norm_sq]
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_pow]
    rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- The normalized projection has at least the original score in its top-K
Schmidt mass. The same argument bounds the score by the target's top-K mass. -/
theorem projection_schmidtMass_bounds {a b e f : Type*}
    [Fintype a] [Fintype b] [Fintype e] [Fintype f]
    [DecidableEq a] [DecidableEq e]
    (M : Matrix (a × e) (b × f) ℂ) (U : Matrix a b ℂ) (Γ : Matrix e f ℂ)
    {K : ℕ} {t : ℝ} (hM : ‖M‖ = 1) (hU : ‖U‖ = 1) (hΓ : ‖Γ‖ = 1)
    (hrank : M.rank ≤ K) (hinner : frobInner (U ⊗ₖ Γ) M = (t : ℂ)) :
    t ^ 2 ≤ schmidtMass K U ∧ t ^ 2 ≤ schmidtMass K Γ := by
  have h := norm_frobInner_sq_le_schmidtMass (U ⊗ₖ Γ) M hM hrank
  have hi : ‖frobInner M (U ⊗ₖ Γ)‖ ^ 2 = t ^ 2 := by
    rw [← frobInner_conj, hinner]
    simp only [Complex.star_def, Complex.conj_ofReal, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  rw [hi] at h
  exact le_min_iff.mp (h.trans (schmidtMass_kronecker_le_min K U Γ hU hΓ))

/-- Abstract finite-dimensional projection/truncation step. The projection
identity is discharged for the Choi coefficients below. -/
theorem exists_rank_bounded_frozen_tensor {a b e f : Type*}
    [Fintype a] [Fintype b] [Fintype e] [Fintype f]
    [DecidableEq a] [DecidableEq e]
    (M : Matrix (a × e) (b × f) ℂ) (U : Matrix a b ℂ) (Z : Matrix e f ℂ)
    {K : ℕ} (hM : ‖M‖ = 1) (hU : ‖U‖ = 1) (hrank : M.rank ≤ K)
    (hZ : 0 < ‖Z‖)
    (hproj : ∀ G : Matrix e f ℂ, frobInner (U ⊗ₖ G) M = frobInner G Z) :
    ∃ G : Matrix e f ℂ, ‖G‖ = 1 ∧ G.rank ≤ K ∧
      ‖M - U ⊗ₖ G‖ ^ 2 ≤ 2 * (1 - ‖Z‖ ^ 2) := by
  classical
  obtain ⟨Γ, hΓ, hZΓ, hΓZ⟩ := exists_normalized_matrix Z hZ
  have hmass := (projection_schmidtMass_bounds M U Γ hM hU hΓ hrank
    ((hproj Γ).trans hΓZ)).2
  obtain ⟨G, hG, hGrank, hGΓ⟩ := exists_schmidt_truncation Γ K
    (lt_of_lt_of_le (sq_pos_of_pos hZ) hmass)
  refine ⟨G, hG, hGrank, ?_⟩
  have hinner : (frobInner (U ⊗ₖ G) M).re =
      ‖Z‖ * Real.sqrt (schmidtMass K Γ) := by
    conv_lhs =>
      rw [hproj, hZΓ, frobInner_smul_right, hGΓ, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hroot : ‖Z‖ ≤ Real.sqrt (schmidtMass K Γ) := by
    exact (Real.le_sqrt (norm_nonneg _) (schmidtMass_nonneg K Γ)).mpr hmass
  have hprod := mul_le_mul_of_nonneg_left hroot (norm_nonneg Z)
  rw [frobNorm_sub_sq, frobNorm_kronecker, hM, hU, hG, hinner]
  nlinarith

/-- Freezing for a finite dilation with bounded laboratory Choi rank. The
environment vector has Schmidt rank at most K, with no local support bound
assumed and with the exact normalized Frobenius constant `sqrt(2 epsilon)`. -/
theorem exists_rank_bounded_approx_frozen {a b i j e f : Type*}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j] [Fintype e] [Fintype f]
    [DecidableEq a] [DecidableEq b] [DecidableEq i] [DecidableEq j]
    [DecidableEq e] [DecidableEq f] [Nonempty i] [Nonempty j]
    (U : Matrix (a × b) (i × j) ℂ) (F : Matrix ((a × e) × (b × f)) (i × j) ℂ)
    {K : ℕ} {ε : ℝ} (hU : IsIsometry U) (hF : IsIsometry F)
    (hrank : (normalizedLabChoiMatrix F).rank ≤ K) (hε : ε < 1)
    (hscore : 1 - ε ≤ scoreU U (channelOf (F.submatrix (outputRegroup a b e f) id))) :
    ∃ g : e × f → ℂ, IsUnitVector g ∧ schmidtRank g ≤ K ∧
      ‖F - insertResource a b g * U‖ / Real.sqrt (Fintype.card (i × j) : ℝ) ≤
        Real.sqrt (2 * ε) := by
  have hZ : 0 < ‖choiEnvironment U F‖ := by
    have hz := norm_sq_choiEnvironment U F
    nlinarith [norm_nonneg (choiEnvironment U F)]
  have hproj (G : Matrix e f ℂ) :
      frobInner (normalizedLabChoiMatrix U ⊗ₖ G) (tensorChoiMatrix F) =
        frobInner G (choiEnvironment U F) := by
    have h := frobInner_tensorChoiMatrix_frozen U F (fun x => G x.1 x.2)
    rwa [tensorChoiMatrix_frozen] at h
  obtain ⟨G, hG, hGrank, hdist⟩ := exists_rank_bounded_frozen_tensor (K := K)
    (tensorChoiMatrix F) (normalizedLabChoiMatrix U) (choiEnvironment U F)
    (norm_tensorChoiMatrix_of_isometry hF) (norm_normalizedLabChoiMatrix_of_isometry hU)
    (by simpa only [rank_tensorChoiMatrix] using hrank) hZ hproj
  let g : e × f → ℂ := fun x => G x.1 x.2
  have hg : resourceMatrix g = G := rfl
  refine ⟨g, (isUnitVector_iff_norm_resourceMatrix g).mpr (hg ▸ hG), ?_, ?_⟩
  · exact hGrank
  · rw [norm_sq_choiEnvironment] at hdist
    have hle : ‖tensorChoiMatrix F - normalizedLabChoiMatrix U ⊗ₖ G‖ ^ 2 ≤ 2 * ε :=
      hdist.trans (by linarith)
    have hε0 : 0 ≤ 2 * ε := (sq_nonneg _).trans hle
    have h := (Real.le_sqrt (norm_nonneg _) hε0).mpr hle
    rw [← hg, ← tensorChoiMatrix_frozen, ← tensorChoiMatrix_sub, norm_tensorChoiMatrix] at h
    exact h

/-- Any budget-K purified dilation's score is bounded by the target's
top-K Schmidt mass, including score zero. This is the flat-spectrum test's
input, proved without an image-volume assumption. -/
theorem scoreU_le_schmidtMass_of_choiRank {a b i j e f : Type*}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j] [Fintype e] [Fintype f]
    [DecidableEq a] [DecidableEq b] [DecidableEq i] [DecidableEq j]
    [DecidableEq e] [DecidableEq f] [Nonempty i] [Nonempty j]
    (U : Matrix (a × b) (i × j) ℂ) (F : Matrix ((a × e) × (b × f)) (i × j) ℂ)
    {K : ℕ} (hU : IsIsometry U) (hF : IsIsometry F)
    (hrank : (normalizedLabChoiMatrix F).rank ≤ K) :
    scoreU U (channelOf (F.submatrix (outputRegroup a b e f) id)) ≤
      schmidtMass K (normalizedLabChoiMatrix U) := by
  rw [← norm_sq_choiEnvironment]
  by_cases hZ : 0 < ‖choiEnvironment U F‖
  · obtain ⟨Γ, hΓ, _, hΓZ⟩ := exists_normalized_matrix (choiEnvironment U F) hZ
    have hp := frobInner_tensorChoiMatrix_frozen U F (fun x => Γ x.1 x.2)
    rw [tensorChoiMatrix_frozen] at hp
    exact (projection_schmidtMass_bounds (K := K) (tensorChoiMatrix F)
      (normalizedLabChoiMatrix U) Γ (norm_tensorChoiMatrix_of_isometry hF)
      (norm_normalizedLabChoiMatrix_of_isometry hU) hΓ
      (by simpa only [rank_tensorChoiMatrix] using hrank) (hp.trans hΓZ)).1
  · have hz : ‖choiEnvironment U F‖ = 0 := le_antisymm (le_of_not_gt hZ) (norm_nonneg _)
    rw [hz, zero_pow (by decide)]
    exact schmidtMass_nonneg _ _

section Protocol

variable {ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]

/-- Sharp freezing in the original one-round model. The charged footprint
supplies the Choi-rank bound, rather than an additional rank hypothesis. -/
theorem PureProtocol.exists_rank_bounded_approx_frozen [Nonempty ιA] [Nonempty ιB]
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ} {ε : ℝ}
    (hU : IsIsometry U) (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hε : ε < 1) (hscore : 1 - ε ≤ scoreU U P.operationalChannel) :
    ∃ g : εA × εB → ℂ, IsUnitVector g ∧ schmidtRank g ≤ K ∧
      ‖P.globalIsometry - insertResource ιA' ιB' g * U‖ /
        Real.sqrt (Fintype.card (ιA × ιB) : ℝ) ≤ Real.sqrt (2 * ε) :=
  NLQCLean.exists_rank_bounded_approx_frozen U P.globalIsometry hU
    P.isIsometry_globalIsometry (P.rank_normalizedLabChoiMatrix_le_of_hasFootprint hK)
    hε hscore

theorem PureProtocol.scoreU_le_schmidtMass [Nonempty ιA] [Nonempty ιB]
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) {K : ℕ}
    (hU : IsIsometry U) (hK : NLQCLean.HasFootprint K P.resource μA μB) :
    scoreU U P.operationalChannel ≤ schmidtMass K (normalizedLabChoiMatrix U) :=
  scoreU_le_schmidtMass_of_choiRank U P.globalIsometry hU P.isIsometry_globalIsometry
    (P.rank_normalizedLabChoiMatrix_le_of_hasFootprint hK)

end Protocol

end NLQCLean

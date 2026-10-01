import NLQCLean.LinearAlgebra.FlatProductTail
import NLQCLean.Approx.StrongSupport
import NLQCLean.Approx.SharpFreezing
import NLQCLean.Models.ProtocolMetrics
import NLQCLean.Models.SwapChoi
import NLQCLean.Models.SwapNeighborhood

/-!
# Near SWAP, the frozen environment needs only `⌈K/⌈D/2⌉⌉` Schmidt terms

For every pure protocol on arbitrary finite registers with
footprint `K`, every target `U ∈ S_d`, and score at least `1 − e` with `0 ≤ e ≤ 1/16`, there
is a unit environment vector `g` of Schmidt rank at most `s = frozenSupport d K` with

  `‖F − (I ⊗ g) U‖_F / d ≤ √(18 e)`.

The tail loss is proportional to `e`; no fixed additive truncation error occurs, and all
original environment dimensions are arbitrary. The phase of the projection is preserved.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

theorem normalizedLabChoiMatrix_sub {a b i j : Type*} [Fintype i] [Fintype j]
    (F G : Matrix (a × b) (i × j) ℂ) :
    normalizedLabChoiMatrix (F - G) = normalizedLabChoiMatrix F - normalizedLabChoiMatrix G := by
  ext x y
  simp [normalizedLabChoiMatrix, labChoiMatrix, mul_sub]

/-- Near SWAP: `⌈D/2⌉` squared Schmidt coefficients of `|U⟩⟩` are at least `1/(4D)`. -/
theorem schmidtWeights_flat_of_mem_swapNeighborhood {d : ℕ} (hd : 2 ≤ d)
    {U : Matrix.unitaryGroup (Fin d × Fin d) ℂ} (hU : U ∈ swapNeighborhood d) :
    ∃ S : Finset (Fin d × Fin d), S.card = flatSupportCount d ∧
      ∀ i ∈ S, 1 / (4 * (d : ℝ) ^ 2) ≤
        schmidtWeights (normalizedLabChoiMatrix (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) i := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsqrt : Real.sqrt (Fintype.card (Fin d × Fin d) : ℝ) = d := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    exact Real.sqrt_mul_self hdR.le
  have hW : normalizedLabChoiMatrix (swapUnitary (Fin d)) *
      (normalizedLabChoiMatrix (swapUnitary (Fin d)))ᴴ =
      (((1 / (d : ℝ)) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := by
    rw [normalizedLabChoiMatrix_swapUnitary_gram]
    ext p q
    by_cases h : p = q
    · subst h
      simp [Fintype.card_prod, Fintype.card_fin, sq]
    · simp [h]
  have hdist : ‖normalizedLabChoiMatrix (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
      normalizedLabChoiMatrix (swapUnitary (Fin d))‖ ≤ 1 / 4 := by
    rw [← normalizedLabChoiMatrix_sub, norm_normalizedLabChoiMatrix, hsqrt]
    exact hU
  have hsum := sum_sq_sqrt_schmidtWeights_sub_le
    (normalizedLabChoiMatrix (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ))
    (normalizedLabChoiMatrix (swapUnitary (Fin d))) (by positivity) hW
  have h16 : ∑ i, (Real.sqrt (schmidtWeights
      (normalizedLabChoiMatrix (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) i) - 1 / d) ^ 2 ≤
      1 / 16 := by
    refine hsum.trans ?_
    have hn := norm_nonneg (normalizedLabChoiMatrix
      (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - normalizedLabChoiMatrix (swapUnitary (Fin d)))
    nlinarith
  exact exists_flat_support hd (by simp [Fintype.card_prod, sq]) _ h16

theorem schmidtMass_kronecker_eq_topWeightMass {m n p q : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq p]
    (K : ℕ) (M : Matrix m n ℂ) (N : Matrix p q ℂ) :
    schmidtMass K (M ⊗ₖ N) =
      topWeightMass K (fun i : m × p ↦ schmidtWeights M i.1 * schmidtWeights N i.2) := by
  obtain ⟨V, hV, hV', hgramM⟩ := exists_schmidt_coordinates M
  obtain ⟨U, hU, hU', hgramN⟩ := exists_schmidt_coordinates N
  have hVU' : IsIsometry (V ⊗ₖ U)ᴴ := by
    rw [Matrix.conjTranspose_kronecker]
    exact hV'.kronecker hU'
  have hgram : ((V ⊗ₖ U)ᴴ * (M ⊗ₖ N)) * ((V ⊗ₖ U)ᴴ * (M ⊗ₖ N))ᴴ =
      Matrix.diagonal (fun i : m × p ↦
        ((schmidtWeights M i.1 * schmidtWeights N i.2 : ℝ) : ℂ)) := by
    simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      hgramM, hgramN, Matrix.diagonal_kronecker_diagonal, Complex.ofReal_mul]
  exact schmidtMass_eq_topWeightMass_of_coordinates (M ⊗ₖ N) (V ⊗ₖ U)
    (fun i : m × p ↦ schmidtWeights M i.1 * schmidtWeights N i.2)
    (hV.kronecker hU) hVU' (fun i ↦ mul_nonneg (schmidtWeights_nonneg M _)
      (schmidtWeights_nonneg N _)) hgram K

/-- Abstract step: a flat logical factor lets the projection be truncated to rank `s`
with squared loss at most `18 ε`. -/
theorem exists_small_support_frozen_tensor {a b e f : Type*}
    [Fintype a] [Fintype b] [Fintype e] [Fintype f] [DecidableEq a] [DecidableEq e]
    [DecidableEq b] [DecidableEq f]
    (M : Matrix (a × e) (b × f) ℂ) (U : Matrix a b ℂ) (Z : Matrix e f ℂ)
    {K q s : ℕ} (hq : 0 < q) (hKs : K ≤ q * s) {c ε : ℝ} (hc : 0 < c) (hcq : 1 / 8 ≤ c * q)
    (hε : ε ≤ 1 / 16) (hM : ‖M‖ = 1) (hU : ‖U‖ = 1) (hrank : M.rank ≤ K)
    (hZ : 1 - ε ≤ ‖Z‖ ^ 2) (hZ1 : ‖Z‖ ≤ 1)
    (hproj : ∀ G : Matrix e f ℂ, frobInner (U ⊗ₖ G) M = frobInner G Z)
    (S : Finset a) (hS : S.card = q) (hflat : ∀ i ∈ S, c ≤ schmidtWeights U i) :
    ∃ G : Matrix e f ℂ, ‖G‖ = 1 ∧ G.rank ≤ s ∧ ‖M - U ⊗ₖ G‖ ^ 2 ≤ 18 * ε := by
  have hZpos : 0 < ‖Z‖ := by nlinarith [norm_nonneg Z]
  obtain ⟨Γ, hΓ, hZΓ, hΓZ⟩ := exists_normalized_matrix Z hZpos
  have hinner : frobInner (U ⊗ₖ Γ) M = (‖Z‖ : ℂ) := (hproj Γ).trans hΓZ
  have hK : ‖Z‖ ^ 2 ≤ schmidtMass K (U ⊗ₖ Γ) := by
    have h := norm_frobInner_sq_le_schmidtMass (U ⊗ₖ Γ) M hM hrank
    have hi : ‖frobInner M (U ⊗ₖ Γ)‖ ^ 2 = ‖Z‖ ^ 2 := by
      rw [← frobInner_conj, hinner]
      simp only [Complex.star_def, Complex.conj_ofReal, Complex.norm_real, Real.norm_eq_abs,
        sq_abs]
    rwa [hi] at h
  rw [schmidtMass_kronecker_eq_topWeightMass] at hK
  have hp1 : ∑ i, schmidtWeights U i = 1 := by rw [sum_schmidtWeights, hU, one_pow]
  have hz1 : ∑ j, schmidtWeights Γ j = 1 := by rw [sum_schmidtWeights, hΓ, one_pow]
  have htail := topWeightMass_product_le_of_flat (s := s) hq hKs hc _ _
    (schmidtWeights_nonneg U) (schmidtWeights_nonneg Γ) hp1 hz1 S hS hflat
  have h1 : c * q * (1 - topWeightMass s (schmidtWeights Γ)) ≤ ε := by nlinarith
  have ht1 : topWeightMass s (schmidtWeights Γ) ≤ 1 :=
    (topWeightMass_le_sum s _ (schmidtWeights_nonneg Γ)).trans hz1.le
  have ht8 : 1 - 8 * ε ≤ topWeightMass s (schmidtWeights Γ) := by nlinarith
  have hmass : schmidtMass s Γ = topWeightMass s (schmidtWeights Γ) := rfl
  have htpos : 0 < schmidtMass s Γ := by rw [hmass]; linarith
  obtain ⟨G, hG, hGrank, hGΓ⟩ := exists_schmidt_truncation Γ s htpos
  refine ⟨G, hG, hGrank, ?_⟩
  have hre : (frobInner (U ⊗ₖ G) M).re = ‖Z‖ * Real.sqrt (schmidtMass s Γ) := by
    conv_lhs => rw [hproj, hZΓ, frobInner_smul_right, hGΓ, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hnorm : ‖U ⊗ₖ G‖ = 1 := by rw [frobNorm_kronecker, hU, hG, one_mul]
  rw [frobNorm_sub_sq, hM, hnorm, hre]
  rw [hmass] at htpos ⊢
  set t := topWeightMass s (schmidtWeights Γ)
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt htpos.le
  have hs0 := Real.sqrt_nonneg t
  have hs1 : Real.sqrt t ≤ 1 := by nlinarith
  have hs2 : t ≤ Real.sqrt t := by nlinarith
  have hz2 : ‖Z‖ ^ 2 ≤ ‖Z‖ := by nlinarith [norm_nonneg Z]
  have hprod : (1 - ε) * (1 - 8 * ε) ≤ ‖Z‖ ^ 2 * t :=
    mul_le_mul hZ ht8 (by linarith) (by positivity)
  have hmono : ‖Z‖ ^ 2 * t ≤ ‖Z‖ * Real.sqrt t := mul_le_mul hz2 hs2 htpos.le (norm_nonneg _)
  nlinarith

section Protocol

variable {d : ℕ} {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- Freezing: near SWAP, a rank-`⌈K/⌈D/2⌉⌉` frozen environment approximates the protocol with
normalized Frobenius residual at most `√(18 e)`. -/
theorem PureProtocol.exists_small_support_approx_frozen
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB) (hd : 2 ≤ d)
    {U : Matrix.unitaryGroup (Fin d × Fin d) ℂ} (hU : U ∈ swapNeighborhood d)
    {K : ℕ} (hK : P.HasFootprint K) {e : ℝ} (he0 : 0 ≤ e) (he : e ≤ 1 / 16)
    (hscore : 1 - e ≤ scoreU (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) P.operationalChannel) :
    ∃ g : εA × εB → ℂ, IsUnitVector g ∧ schmidtRank g ≤ frozenSupport d K ∧
      ‖P.globalIsometry - insertResource (Fin d) (Fin d) g *
          (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)‖ / d ≤ Real.sqrt (18 * e) := by
  have hd0 : 0 < d := by omega
  have : NeZero d := ⟨hd0.ne'⟩
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hUiso : IsIsometry (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
    Matrix.mem_unitaryGroup_iff'.mp U.2
  have hF := P.isIsometry_globalIsometry
  have hproj (G : Matrix εA εB ℂ) :
      frobInner (normalizedLabChoiMatrix (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ G)
        (tensorChoiMatrix P.globalIsometry) =
      frobInner G (choiEnvironment (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
        P.globalIsometry) := by
    have h := frobInner_tensorChoiMatrix_frozen (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
      P.globalIsometry (fun x => G x.1 x.2)
    rwa [tensorChoiMatrix_frozen] at h
  have hZsq := norm_sq_choiEnvironment (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    P.globalIsometry
  have hscore1 : scoreU (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) P.operationalChannel ≤ 1 :=
    scoreU_le_one hUiso (isIsometry_globalIsometryRegrouped P.resource_unit P.encA_isometry
      P.encB_isometry P.decA_isometry P.decB_isometry)
  have hZ1 : ‖choiEnvironment (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) P.globalIsometry‖ ≤ 1 := by
    have h : ‖choiEnvironment (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
        P.globalIsometry‖ ^ 2 ≤ 1 := hZsq.trans_le hscore1
    nlinarith [norm_nonneg (choiEnvironment (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
      P.globalIsometry)]
  obtain ⟨S, hS, hflat⟩ := schmidtWeights_flat_of_mem_swapNeighborhood hd hU
  have hq := flatSupportCount_pos hd0
  have hKs := le_flatSupportCount_mul_frozenSupport hd0 K
  have hcq : 1 / 8 ≤ 1 / (4 * (d : ℝ) ^ 2) * flatSupportCount d := by
    have h2 : ((d ^ 2 : ℕ) : ℝ) ≤ ((2 * flatSupportCount d : ℕ) : ℝ) := by
      exact_mod_cast sq_le_two_mul_flatSupportCount d
    push_cast at h2
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    nlinarith
  obtain ⟨G, hG, hGrank, hdist⟩ := exists_small_support_frozen_tensor
    (tensorChoiMatrix P.globalIsometry)
    (normalizedLabChoiMatrix (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ))
    (choiEnvironment (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) P.globalIsometry)
    hq hKs (by positivity) hcq he (norm_tensorChoiMatrix_of_isometry hF)
    (norm_normalizedLabChoiMatrix_of_isometry hUiso)
    (by simpa only [rank_tensorChoiMatrix] using P.rank_normalizedLabChoiMatrix_le_of_hasFootprint hK)
    (by rw [hZsq]; exact hscore) hZ1 hproj S hS hflat
  let g : εA × εB → ℂ := fun x => G x.1 x.2
  have hg : resourceMatrix g = G := rfl
  refine ⟨g, (isUnitVector_iff_norm_resourceMatrix g).mpr (hg ▸ hG), hGrank, ?_⟩
  have hsqrt : Real.sqrt (Fintype.card (Fin d × Fin d) : ℝ) = d := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    exact Real.sqrt_mul_self hdR.le
  have hle := (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hdist
  rw [← hg, ← tensorChoiMatrix_frozen, ← tensorChoiMatrix_sub, norm_tensorChoiMatrix, hsqrt] at hle
  exact hle

end Protocol

end NLQCLean

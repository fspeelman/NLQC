import NLQCLean.Geometry.FiniteDimensionalNets
import NLQCLean.Geometry.EuclideanBallCaps
import NLQCLean.Geometry.AdjointEuclideanCoordinates
import NLQCLean.LinearAlgebra.ResidualSpectralCutoff
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The operator-small Hermitian and skew-Hermitian sectors

With `D = card n` and `0 < R ≤ √D/64`,

  `vol(B_R) ≤ 2 · vol{Q = Qᴴ : ‖Q‖_F < R, ‖Q‖_op ≤ 1/2}`

in the orthonormal real Frobenius coordinates of `HermitianFrobenius n` (real dimension `D²`),
and the same for `SkewFrobenius n` via multiplication by `i`.

Proof: a Hermitian operator norm is attained by a quadratic form at an eigenvector; a
`1/4`-net of the complex unit sphere (at most `9^(2D)` points) then gives
`‖Q‖_op ≤ 2 max_v |v*Qv|`. Each `Q ↦ v*Qv` is the real Frobenius inner product with the
unit-norm projector `vv*`, so the cap lemma and a union bound leave a bad fraction at most
`2 · 9^(2D) exp(−D²/(32R²)) ≤ 2 exp(−122 D) ≤ 1/2`.
-/

namespace NLQCLean

open Matrix MeasureTheory Metric Module
open scoped Matrix.Norms.Frobenius ENNReal

section Quadratic

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem norm_inner_toCLM_sub_le (Q : Matrix n n ℂ) (u v : EuclideanSpace ℂ n) :
    ‖inner ℂ u (toCLM Q u) - inner ℂ v (toCLM Q v)‖ ≤ ‖u - v‖ * opNorm Q * (‖u‖ + ‖v‖) := by
  have hsplit : inner ℂ u (toCLM Q u) - inner ℂ v (toCLM Q v) =
      inner ℂ (u - v) (toCLM Q u) + inner ℂ v (toCLM Q (u - v)) := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    ring
  rw [hsplit]
  have h1 : ‖inner ℂ (u - v) (toCLM Q u)‖ ≤ ‖u - v‖ * (opNorm Q * ‖u‖) :=
    (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (norm_toCLM_le Q u) (norm_nonneg _))
  have h2 : ‖inner ℂ v (toCLM Q (u - v))‖ ≤ ‖v‖ * (opNorm Q * ‖u - v‖) :=
    (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (norm_toCLM_le Q (u - v)) (norm_nonneg _))
  calc _ ≤ ‖inner ℂ (u - v) (toCLM Q u)‖ + ‖inner ℂ v (toCLM Q (u - v))‖ := norm_add_le _ _
    _ ≤ ‖u - v‖ * (opNorm Q * ‖u‖) + ‖v‖ * (opNorm Q * ‖u - v‖) := add_le_add h1 h2
    _ = _ := by ring

/-- A Hermitian operator norm is attained by a quadratic form. -/
theorem exists_unit_opNorm_le_abs_re_inner [Nonempty n] {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) :
    ∃ u : EuclideanSpace ℂ n, ‖u‖ = 1 ∧ opNorm Q ≤ |(inner ℂ u (toCLM Q u)).re| := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => |hQ.eigenvalues i|)
    Finset.univ_nonempty
  let U : Matrix n n ℂ := (hQ.eigenvectorUnitary : Matrix n n ℂ)
  have hU : IsIsometry U := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hQ.eigenvectorUnitary.2
    simpa [IsIsometry, U, Matrix.star_eq_conjTranspose] using h
  have hU' : IsIsometry Uᴴ := by
    have h := Matrix.mem_unitaryGroup_iff.mp hQ.eigenvectorUnitary.2
    simpa [IsIsometry, U, Matrix.star_eq_conjTranspose] using h
  have hspec : Q = U * Matrix.diagonal (RCLike.ofReal ∘ hQ.eigenvalues) * Uᴴ := by
    conv_lhs => rw [hQ.spectral_theorem]
    simp [U, Matrix.star_eq_conjTranspose]
  have hop : opNorm Q ≤ |hQ.eigenvalues j| :=
    (congrArg opNorm hspec).le.trans ((opNorm_unitary_conj_le hU hU' _).trans
      (opNorm_diagonal_le (abs_nonneg _) fun i => by simpa using hj i (Finset.mem_univ _)))
  let u : EuclideanSpace ℂ n := hQ.eigenvectorBasis j
  have hu : ‖u‖ = 1 := hQ.eigenvectorBasis.orthonormal.1 j
  have hTu : toCLM Q u = (hQ.eigenvalues j : ℝ) • u := by
    have h := hQ.mulVec_eigenvectorBasis j
    rw [toCLM_apply]
    ext i
    simpa using congrFun h i
  refine ⟨u, hu, ?_⟩
  rw [hTu, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right, inner_self_eq_norm_sq_to_K, hu]
  simpa using hop

/-- The rank-one projector `v v*`. -/
def rankOneProjector (v : EuclideanSpace ℂ n) : Matrix n n ℂ :=
  Matrix.of fun i k => v i * star (v k)

omit [Fintype n] [DecidableEq n] in
theorem star_rankOneProjector (v : EuclideanSpace ℂ n) :
    star (rankOneProjector v) = rankOneProjector v := by
  ext i k
  simp [rankOneProjector, Matrix.star_apply, mul_comm]

theorem frobInner_rankOneProjector (v : EuclideanSpace ℂ n) (Q : Matrix n n ℂ) :
    frobInner (rankOneProjector v) Q = inner ℂ v (toCLM Q v) := by
  rw [toCLM_apply, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [frobInner, rankOneProjector, Matrix.of_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, star_mul', star_star, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem norm_rankOneProjector (v : EuclideanSpace ℂ n) :
    ‖rankOneProjector v‖ = ‖v‖ ^ 2 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [frobNorm_sq, EuclideanSpace.norm_sq_eq, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp [rankOneProjector, mul_pow]

theorem realFrobeniusInner_rankOneProjector (v : EuclideanSpace ℂ n) (Q : Matrix n n ℂ) :
    inner ℝ (rankOneProjector v) Q = (inner ℂ v (toCLM Q v)).re := by
  rw [realFrobeniusInner_eq_re, frobInner_rankOneProjector]

theorem opNorm_smul (c : ℂ) (A : Matrix n n ℂ) : opNorm (c • A) = ‖c‖ * opNorm A := by
  have h : toCLM (c • A) = c • toCLM A := by
    ext x i
    simp [toCLM_apply, Matrix.smul_mulVec]
  rw [opNorm, h, norm_smul]
  rfl

end Quadratic

section Sector

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The operator-small Hermitian sector inside the Frobenius ball. -/
def hermitianOperatorSector (R : ℝ) : Set (HermitianFrobenius n) :=
  {Q | opNorm (Q : Matrix n n ℂ) ≤ 1 / 2} ∩ ball 0 R

/-- The operator-small skew-Hermitian sector inside the Frobenius ball. -/
def skewOperatorSector (R : ℝ) : Set (SkewFrobenius n) :=
  {A | opNorm (A : Matrix n n ℂ) ≤ 1 / 2} ∩ ball 0 R

theorem exp_net_union_bound {D : ℕ} (hD : 1 ≤ D) {R c : ℝ} (hR : 0 < R)
    (hRD : R ≤ Real.sqrt D / 64) (hc : c ≤ 9 ^ (2 * D)) :
    c * (2 * Real.exp (-((D ^ 2 : ℕ) * (1 / 4 : ℝ) ^ 2 / (2 * R ^ 2)))) ≤ 1 / 2 := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hR2 : R ^ 2 ≤ D / 4096 := by
    have h := pow_le_pow_left₀ hR.le hRD 2
    rw [div_pow, Real.sq_sqrt hDpos.le] at h
    linarith
  have hexp1 : -((D ^ 2 : ℕ) * (1 / 4 : ℝ) ^ 2 / (2 * R ^ 2)) ≤ -(128 * D) := by
    rw [neg_le_neg_iff, le_div_iff₀ (by positivity)]
    push_cast
    nlinarith
  have h9 : (9 : ℝ) ≤ Real.exp 3 := by
    have h := Real.exp_one_gt_d9
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h' := pow_lt_pow_left₀ h (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)
    rw [h3]
    norm_num at h'
    linarith
  have hc' : c ≤ Real.exp (6 * D) := by
    refine hc.trans ?_
    calc (9 : ℝ) ^ (2 * D) ≤ Real.exp 3 ^ (2 * D) := pow_le_pow_left₀ (by norm_num) h9 _
      _ = Real.exp (6 * D) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h122 : Real.exp (-122 : ℝ) ≤ 1 / 4 := by
    have h := Real.add_one_le_exp (122 : ℝ)
    rw [Real.exp_neg]
    rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  calc c * (2 * Real.exp (-((D ^ 2 : ℕ) * (1 / 4 : ℝ) ^ 2 / (2 * R ^ 2))))
      ≤ Real.exp (6 * D) * (2 * Real.exp (-(128 * D))) :=
        mul_le_mul hc' (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp1) (by norm_num))
          (by positivity) (Real.exp_pos _).le
    _ = 2 * Real.exp (-(122 * D)) := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
    _ ≤ 2 * Real.exp (-122) := by
        gcongr
        have : (1 : ℝ) ≤ D := by exact_mod_cast hD
        linarith
    _ ≤ 1 / 2 := by linarith

/-- The operator-small Hermitian sector has at least half the Frobenius ball volume. -/
theorem volume_ball_le_two_mul_hermitianOperatorSector {R : ℝ} (hR : 0 < R)
    (hRD : R ≤ Real.sqrt (Fintype.card n) / 64) :
    volume (ball (0 : HermitianFrobenius n) R) ≤ 2 * volume (hermitianOperatorSector n R) := by
  have hD : 1 ≤ Fintype.card n := by
    by_contra h
    have h0 : Fintype.card n = 0 := by omega
    rw [h0, Nat.cast_zero, Real.sqrt_zero, zero_div] at hRD
    linarith
  have : Nonempty n := Fintype.card_pos_iff.mp hD
  obtain ⟨F, hFA, hcard, hnet⟩ := exists_finset_net_of_subset_closedBall
    (E := EuclideanSpace ℂ n) (A := sphere 0 1)
    (fun x hx => (mem_sphere_zero_iff_norm.mp hx).le) (η := 1 / 4) (by norm_num)
  have hfin : finrank ℝ (EuclideanSpace ℂ n) = 2 * Fintype.card n := by
    rw [finrank_real_of_complex, finrank_euclideanSpace]
  rw [hfin, show (1 : ℝ) + 2 / (1 / 4) = 9 by norm_num] at hcard
  let w : EuclideanSpace ℂ n → HermitianFrobenius n := fun v =>
    ⟨rankOneProjector v, star_rankOneProjector v⟩
  have hw : ∀ v ∈ F, ‖w v‖ ≤ 1 := fun v hv => by
    have hv1 : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp (hFA v hv)
    change ‖rankOneProjector v‖ ≤ 1
    rw [norm_rankOneProjector, hv1, one_pow]
  have hinner : ∀ v (Q : HermitianFrobenius n),
      inner ℝ (w v) Q = (inner ℂ v (toCLM (Q : Matrix n n ℂ) v)).re := fun v Q => by
    rw [Submodule.coe_inner]
    exact realFrobeniusInner_rankOneProjector v Q
  have hcover : ball (0 : HermitianFrobenius n) R ⊆ hermitianOperatorSector n R ∪
      ⋃ v ∈ F, ({Q : HermitianFrobenius n | 1 / 4 ≤ |inner ℝ (w v) Q|} ∩ ball 0 R) := by
    intro Q hQ
    by_cases hop : opNorm (Q : Matrix n n ℂ) ≤ 1 / 2
    · exact Or.inl ⟨hop, hQ⟩
    right
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, not_exists, not_and] at hnot
    have hsmall : ∀ v ∈ F, |(inner ℂ v (toCLM (Q : Matrix n n ℂ) v)).re| < 1 / 4 := fun v hv => by
      rw [← hinner]
      exact not_le.mp fun h => hnot v hv h hQ
    have hherm : (Q : Matrix n n ℂ).IsHermitian := Q.2
    obtain ⟨u, hu, hle⟩ := exists_unit_opNorm_le_abs_re_inner hherm
    obtain ⟨v, hvF, huv⟩ := hnet u (mem_sphere_zero_iff_norm.mpr hu)
    have hv1 : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp (hFA v hvF)
    have hdiff := norm_inner_toCLM_sub_le (Q : Matrix n n ℂ) u v
    rw [hu, hv1] at hdiff
    have hre : |(inner ℂ u (toCLM (Q : Matrix n n ℂ) u)).re| ≤
        |(inner ℂ v (toCLM (Q : Matrix n n ℂ) v)).re| +
          ‖inner ℂ u (toCLM (Q : Matrix n n ℂ) u) - inner ℂ v (toCLM (Q : Matrix n n ℂ) v)‖ := by
      have h1 := Complex.abs_re_le_norm
        (inner ℂ u (toCLM (Q : Matrix n n ℂ) u) - inner ℂ v (toCLM (Q : Matrix n n ℂ) v))
      rw [Complex.sub_re] at h1
      have h2 := abs_sub_abs_le_abs_sub (inner ℂ u (toCLM (Q : Matrix n n ℂ) u)).re
        (inner ℂ v (toCLM (Q : Matrix n n ℂ) v)).re
      linarith
    have hsm := hsmall v hvF
    have hopn := opNorm_nonneg (Q : Matrix n n ℂ)
    have hq : ‖u - v‖ * opNorm (Q : Matrix n n ℂ) * (1 + 1) ≤ 1 / 4 * opNorm (Q : Matrix n n ℂ) * 2 := by
      nlinarith
    rw [not_le] at hop
    linarith
  let e : ℝ := Real.exp (-((finrank ℝ (HermitianFrobenius n) : ℝ) * (1 / 4 : ℝ) ^ 2 / (2 * R ^ 2)))
  have hcap : ∀ v ∈ F, volume ({Q : HermitianFrobenius n | 1 / 4 ≤ |inner ℝ (w v) Q|} ∩ ball 0 R) ≤
      2 * ENNReal.ofReal e * volume (ball (0 : HermitianFrobenius n) R) := fun v hv =>
    volume_cap_le (hw v hv) (by norm_num) hR
  have hdimH : finrank ℝ (HermitianFrobenius n) = Fintype.card n ^ 2 :=
    (finrank_adjoint_matrix_spaces n).1
  have hreal : (F.card : ℝ) * (2 * e) ≤ 1 / 2 := by
    have h := exp_net_union_bound hD hR hRD hcard
    simpa only [e, hdimH] using h
  have hfac : (F.card : ℝ≥0∞) * (2 * ENNReal.ofReal e) ≤ 2⁻¹ := by
    have h2 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
      rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
    rw [h2, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hreal
  set B := volume (ball (0 : HermitianFrobenius n) R) with hB
  have hBfin : B ≠ ⊤ := measure_ball_lt_top.ne
  have hmain : B ≤ volume (hermitianOperatorSector n R) + 2⁻¹ * B := by
    calc B ≤ volume (hermitianOperatorSector n R ∪
          ⋃ v ∈ F, ({Q : HermitianFrobenius n | 1 / 4 ≤ |inner ℝ (w v) Q|} ∩ ball 0 R)) :=
          measure_mono hcover
      _ ≤ volume (hermitianOperatorSector n R) +
          volume (⋃ v ∈ F, ({Q : HermitianFrobenius n | 1 / 4 ≤ |inner ℝ (w v) Q|} ∩ ball 0 R)) :=
          measure_union_le _ _
      _ ≤ volume (hermitianOperatorSector n R) + ∑ v ∈ F, 2 * ENNReal.ofReal e * B := by
          gcongr
          exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum hcap)
      _ = volume (hermitianOperatorSector n R) + (F.card : ℝ≥0∞) * (2 * ENNReal.ofReal e) * B := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ volume (hermitianOperatorSector n R) + 2⁻¹ * B := by gcongr
  have h2B : B + B ≤ 2 * volume (hermitianOperatorSector n R) + B := by
    calc B + B = 2 * B := (two_mul B).symm
      _ ≤ 2 * (volume (hermitianOperatorSector n R) + 2⁻¹ * B) := by gcongr
      _ = 2 * volume (hermitianOperatorSector n R) + B := by
          rw [mul_add, ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  exact ENNReal.le_of_add_le_add_right hBfin h2B

/-- Multiplication by `i` from Hermitian to skew-Hermitian Frobenius coordinates. -/
noncomputable def hermitianToSkew : HermitianFrobenius n ≃ₗᵢ[ℝ] SkewFrobenius n where
  toFun Q := ⟨Complex.I • (Q : Matrix n n ℂ), by
    change star (Complex.I • (Q : Matrix n n ℂ)) = -(Complex.I • (Q : Matrix n n ℂ))
    rw [star_smul, (show IsSelfAdjoint (Q : Matrix n n ℂ) from Q.2).star_eq, Complex.star_def,
      Complex.conj_I, neg_smul]⟩
  invFun A := ⟨(-Complex.I) • (A : Matrix n n ℂ), by
    change star ((-Complex.I) • (A : Matrix n n ℂ)) = (-Complex.I) • (A : Matrix n n ℂ)
    rw [star_smul, (show star (A : Matrix n n ℂ) = -(A : Matrix n n ℂ) from A.2), star_neg,
      Complex.star_def, Complex.conj_I, smul_neg, neg_smul, neg_neg, neg_smul]⟩
  left_inv Q := Subtype.ext (by simp [smul_smul])
  right_inv A := Subtype.ext (by simp [smul_smul])
  map_add' Q R := Subtype.ext (by simp [smul_add])
  map_smul' c Q := Subtype.ext (by simp [smul_comm c Complex.I])
  norm_map' Q := by
    change ‖Complex.I • (Q : Matrix n n ℂ)‖ = ‖(Q : Matrix n n ℂ)‖
    rw [norm_smul, Complex.norm_I, one_mul]

/-- The operator-small skew-Hermitian sector has at least half the Frobenius ball volume. -/
theorem volume_ball_le_two_mul_skewOperatorSector {R : ℝ} (hR : 0 < R)
    (hRD : R ≤ Real.sqrt (Fintype.card n) / 64) :
    volume (ball (0 : SkewFrobenius n) R) ≤ 2 * volume (skewOperatorSector n R) := by
  let e := hermitianToSkew n
  have hmp : MeasurePreserving e volume volume := e.measurePreserving
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hball : e ⁻¹' ball (0 : SkewFrobenius n) R = ball 0 R := by
    rw [LinearIsometryEquiv.preimage_ball, map_zero]
  have hsector : e ⁻¹' skewOperatorSector n R = hermitianOperatorSector n R := by
    rw [skewOperatorSector, Set.preimage_inter, hball, hermitianOperatorSector]
    congr 1
    ext Q
    change opNorm (Complex.I • (Q : Matrix n n ℂ)) ≤ 1 / 2 ↔ _
    rw [opNorm_smul, Complex.norm_I, one_mul]
    rfl
  rw [← hmp.measure_preimage_emb hemb, ← hmp.measure_preimage_emb hemb, hball, hsector]
  exact volume_ball_le_two_mul_hermitianOperatorSector n hR hRD

end Sector

end NLQCLean

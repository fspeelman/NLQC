import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.Geometry.StrongPolynomialTubeConditional

/-!
# The transverse tube estimate for polynomial formats (`prop:tube`)

Let `W ⊆ ℝ^P` be the source of a format with at most `c` constraints of degree at most
`Δ ≥ 2` inside the radius-`R` ball, and `T̂ : ℝ^P → ℝ^{2N}` (`N = d⁴`, normalized Frobenius
output coordinates `H/d`) a polynomial map of degree at most `Δ` whose derivative at every
point of `W` splits as `A + B` with `rank A ≤ ℓ`, `‖dT̂‖ ≤ Λ` and `‖B‖ ≤ λ`, the variational
form of `σ₁ ≤ Λ`, `σ_{ℓ+1} ≤ λ`. If every target of a Borel set `S ⊆ U(d²)` lies within
normalized distance `τ` of `T̂(W)` and `τ + λ ≤ s ≤ 1/64`, then
`μ(S) ≤ exp(C(P + N)) (Λ + 3s)^ℓ s^(N − ℓ)` with `C` depending only on `c`, `Δ` and `R`.

The proof thickens `(x, Y) ↦ T̂(x) + 2sY` over `W × B₁`, applies the general polynomial
image-volume bound to it, and compares with the normal-volume lower bound for the `s`-tube.
-/

namespace NLQCLean

open MvPolynomial MeasureTheory Metric
open scoped ENNReal

namespace DirectVolume

variable {a c Δ : ℕ}

/-- Append the unit-ball inequality in the new coordinates. -/
noncomputable def PolyFormat.thicken (F : PolyFormat a c Δ) (m : ℕ) (hΔ : 2 ≤ Δ) :
    PolyFormat (a + m) (c + 1) Δ where
  numEquations := F.numEquations
  numInequalities := F.numInequalities + 1
  constraint_count := by have := F.constraint_count; omega
  equations i := rename (Fin.castAdd m) (F.equations i)
  inequalities := Fin.cases (thickeningBallPolynomial a m)
    (fun i => rename (Fin.castAdd m) (F.inequalities i))
  equations_degree i := (totalDegree_rename_le _ _).trans (F.equations_degree i)
  inequalities_degree := Fin.cases ((thickeningBallPolynomial_degree a m).trans hΔ)
    (fun i => (totalDegree_rename_le _ _).trans (F.inequalities_degree i))

theorem PolyFormat.mem_thicken_source {m : ℕ} (F : PolyFormat a c Δ) (hΔ : 2 ≤ Δ)
    (z : RealEuclidean (a + m)) :
    z ∈ (F.thicken m hΔ).source ↔
      (euclideanProductCoordinates a m z).fst ∈ F.source ∧
        ‖(euclideanProductCoordinates a m z).snd‖ ≤ 1 := by
  simp only [PolyFormat.source, Set.mem_ofPred_eq, PolyFormat.thicken, Fin.forall_fin_succ,
    Fin.cases_zero, Fin.cases_succ, eval_rename, thickeningBallPolynomial_eval,
    Function.comp_def]
  simp only [← euclideanProductCoordinates_fst_apply]
  have hb : 0 ≤ 1 - ‖(euclideanProductCoordinates a m z).snd‖ ^ 2 ↔
      ‖(euclideanProductCoordinates a m z).snd‖ ≤ 1 := by
    have hn := norm_nonneg (euclideanProductCoordinates a m z).snd
    constructor <;> intro h <;> nlinarith
  rw [hb]
  tauto

theorem PolyFormat.thicken_source_radius {m : ℕ} (F : PolyFormat a c Δ) (hΔ : 2 ≤ Δ)
    {R : ℝ} (hR : 0 ≤ R) (h3 : F.source ⊆ closedBall 0 R) :
    (F.thicken m hΔ).source ⊆ closedBall 0 (R + 1) := by
  intro z hz
  obtain ⟨hx, hy⟩ := (F.mem_thicken_source hΔ z).mp hz
  have hx' : ‖(euclideanProductCoordinates a m z).fst‖ ≤ R := by simpa using h3 hx
  have he := WithLp.prod_norm_sq_eq_of_L2 (euclideanProductCoordinates a m z)
  rw [(euclideanProductCoordinates a m).norm_map] at he
  rw [mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg z, norm_nonneg (euclideanProductCoordinates a m z).fst,
    norm_nonneg (euclideanProductCoordinates a m z).snd]

variable {m : ℕ}

/-- The coordinate polynomial for `(x, Y) ↦ p(x) + cY`. -/
noncomputable def PolyMap.thicken (p : PolyMap a m Δ) (c : ℝ) (hΔ : 1 ≤ Δ) :
    PolyMap (a + m) m Δ where
  coordinates j := rename (Fin.castAdd m) (p.coordinates j) + C c * X (j.natAdd a)
  degree_le j := (totalDegree_add _ _).trans (max_le
    ((totalDegree_rename_le _ _).trans (p.degree_le j))
    ((totalDegree_mul _ _).trans (by simpa using hΔ)))

theorem PolyMap.thicken_eval (p : PolyMap a m Δ) (c : ℝ) (hΔ : 1 ≤ Δ)
    (z : RealEuclidean (a + m)) :
    (p.thicken c hΔ).eval z = p.eval (euclideanProductCoordinates a m z).fst +
      c • (euclideanProductCoordinates a m z).snd := by
  ext j
  simp [PolyMap.eval, PolyMap.thicken, eval_rename, Function.comp_def,
    euclideanProductCoordinates_fst_apply, euclideanProductCoordinates_snd_apply]

theorem PolyMap.tube_subset_thicken_image {c' : ℕ} (p : PolyMap a m Δ) (hΔ : 2 ≤ Δ)
    (F : PolyFormat a c' Δ) {c : ℝ} (hc : 0 < c) :
    {y | ∃ x ∈ F.source, dist y (p.eval x) < c} ⊆
      (p.thicken c (by omega)).eval '' (F.thicken m hΔ).source := by
  rintro y ⟨x, hx, hy⟩
  let v : RealEuclidean m := c⁻¹ • (y - p.eval x)
  let z := (euclideanProductCoordinates a m).symm (WithLp.toLp 2 (x, v))
  have he : euclideanProductCoordinates a m z = WithLp.toLp 2 (x, v) :=
    (euclideanProductCoordinates a m).apply_symm_apply _
  refine ⟨z, (F.mem_thicken_source hΔ z).mpr ?_, ?_⟩
  · rw [he]
    refine ⟨hx, ?_⟩
    change ‖v‖ ≤ 1
    dsimp only [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc), inv_mul_eq_div]
    exact (div_le_one hc).mpr (by simpa only [dist_eq_norm] using hy.le)
  · rw [p.thicken_eval, he]
    change p.eval x + c • (c⁻¹ • (y - p.eval x)) = y
    rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul, add_sub_cancel]

theorem PolyMap.hasFDerivAt_thicken (p : PolyMap a m Δ) (c : ℝ) (hΔ : 1 ≤ Δ)
    (z : RealEuclidean (a + m)) {L : RealEuclidean a →L[ℝ] RealEuclidean m}
    (hL : HasFDerivAt p.eval L (euclideanProductCoordinates a m z).fst) :
    HasFDerivAt (p.thicken c hΔ).eval (thickenedLinearMap L c) z := by
  let e := (euclideanProductCoordinates a m).toContinuousLinearEquiv.toContinuousLinearMap
  let f := (WithLp.fstL 2 ℝ (RealEuclidean a) (RealEuclidean m)).comp e
  let g := (WithLp.sndL 2 ℝ (RealEuclidean a) (RealEuclidean m)).comp e
  have h := (hL.comp z f.hasFDerivAt).add (g.hasFDerivAt.const_smul c)
  have he : L.comp f + c • g = thickenedLinearMap L c := by
    apply ContinuousLinearMap.ext
    intro v
    exact (thickenedLinearMap_apply L c v).symm
  rw [he] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun v => p.thicken_eval c hΔ v))

/-- The image-volume constant of a thickened `(c, Δ, R)` format. -/
noncomputable def tubeVolumeConstant (c Δ : ℕ) (R : ℝ) : ℝ :=
  max 4 (R + 1 + 1) * (((2 * Δ + 1) * ((2 * Δ + 2) * 2 ^ (2 * (c + 1) + 1)) : ℕ) : ℝ)

theorem one_le_tubeVolumeConstant (c Δ : ℕ) (R : ℝ) : 1 ≤ tubeVolumeConstant c Δ R := by
  have h1 : (1 : ℝ) ≤ (((2 * Δ + 1) * ((2 * Δ + 2) * 2 ^ (2 * (c + 1) + 1)) : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold tubeVolumeConstant
  nlinarith [le_max_left (4 : ℝ) (R + 1 + 1)]

/-- **`prop:tube`.** The transverse tube estimate for a polynomial witness family of format
`(c, Δ)` in the radius-`R` ball, with the derivative split `dT̂ = A + B`, `rank A ≤ ℓ`,
`‖dT̂‖ ≤ Λ`, `‖B‖ ≤ λ`, every target of `S` within normalized distance `τ` of `T̂(W)`, and
`τ + λ ≤ s ≤ 1/64`. -/
theorem polynomial_tube_haar_le {d P c Δ : ℕ} (hd : 2 ≤ d) (hΔ : 2 ≤ Δ) {R : ℝ} (hR : 0 ≤ R)
    (F : PolyFormat P c Δ) (h3 : F.source ⊆ closedBall 0 R) (T : PolyMap P (2 * d ^ 4) Δ)
    {ℓ : ℕ} (hℓ : ℓ ≤ d ^ 4) {Λ lam : ℝ} (hΛ : 0 ≤ Λ) (hlam : 0 ≤ lam)
    (hsplit : ∀ x ∈ F.source, ∃ A B : RealEuclidean P →L[ℝ] RealEuclidean (2 * d ^ 4),
      fderiv ℝ T.eval x = A + B ∧ Module.finrank ℝ (LinearMap.range A.toLinearMap) ≤ ℓ ∧
      ‖fderiv ℝ T.eval x‖ ≤ Λ ∧ ‖B‖ ≤ lam)
    {τ s : ℝ} (hτ : 0 ≤ τ) (hs : 0 < s) (hs' : s ≤ 1 / 64) (hτs : τ + lam ≤ s)
    {S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ)} (hS : MeasurableSet S)
    (hcover : ∀ U ∈ S, ∃ x ∈ F.source,
      dist (normalizedOutputCoordinates d (U : Matrix _ _ ℂ)) (T.eval x) ≤ τ) :
    unitaryHaar (Fin d × Fin d) S ≤
      ENNReal.ofReal (Real.exp ((36864 * tubeVolumeConstant c Δ R ^ 4) * ((P : ℝ) + d ^ 4)) *
        (Λ + 3 * s) ^ ℓ * s ^ (d ^ 4 - ℓ)) := by
  have hd0 : 0 < d := by omega
  have hN1 : 1 ≤ d ^ 4 := Nat.one_le_pow _ _ hd0
  have hΔ1 : 1 ≤ Δ := by omega
  set CV := tubeVolumeConstant c Δ R with hCV
  have hCV1 : 1 ≤ CV := one_le_tubeVolumeConstant c Δ R
  have hCV0 : 0 ≤ CV := by linarith
  set Λ' := Λ + lam with hΛ'
  have hlamΛ' : lam ≤ Λ' := by linarith
  have hlams : lam ≤ s := by linarith
  have hlow := strong_normalizedWitnessTube_volume_lower hd hs hs' hS
  -- the tube lies in the thickened image
  have hincl : normalizedWitnessTube d s S ⊆
      (T.thicken (2 * s) hΔ1).eval '' (F.thicken (2 * d ^ 4) hΔ).source := by
    refine subset_trans ?_ (T.tube_subset_thicken_image hΔ F (by positivity : (0 : ℝ) < 2 * s))
    rintro y ⟨U, hU, hy⟩
    obtain ⟨x, hx, hdist⟩ := hcover U hU
    refine ⟨x, hx, ?_⟩
    have htri := dist_triangle y (normalizedOutputCoordinates d (U : Matrix _ _ ℂ)) (T.eval x)
    linarith
  -- the image-volume bound for the thickened map
  have hbound : ∀ z ∈ (F.thicken (2 * d ^ 4) hΔ).source,
      topRealJacobian (fderiv ℝ (T.thicken (2 * s) hΔ1).eval z) ≤
        (Λ' + 2 * s) ^ ℓ * (lam + 2 * s) ^ (2 * d ^ 4 - ℓ) := by
    intro z hz
    have hx := ((F.mem_thicken_source hΔ z).mp hz).1
    have hdiff : HasFDerivAt T.eval (fderiv ℝ T.eval (euclideanProductCoordinates P (2 * d ^ 4) z).fst)
        (euclideanProductCoordinates P (2 * d ^ 4) z).fst :=
      ((T.contDiff_eval.differentiable one_ne_zero) _).hasFDerivAt
    rw [(T.hasFDerivAt_thicken (2 * s) hΔ1 z hdiff).fderiv]
    obtain ⟨A, B, hdec, hrank, hnorm, hB⟩ := hsplit _ hx
    exact topRealJacobian_thickenedLinearMap_le _ A B hdec hlam hlamΛ' (by positivity)
      (hnorm.trans (by linarith)) hB hrank (by omega)
  have hup := (measure_mono hincl).trans
    (volume_image_le_of_polyFormat hΔ (F.thicken (2 * d ^ 4) hΔ) (T.thicken (2 * s) hΔ1)
      (by omega) (by linarith : (0 : ℝ) ≤ R + 1)
      (F.thicken_source_radius hΔ hR h3)
      (Nat.one_le_iff_ne_zero.mpr (by positivity)) (pow_add_le_of_polyFormat (c + 1) Δ)
      (by positivity) hbound)
  have hJ := strongJacobian_le hℓ (by linarith : 0 ≤ Λ') hlam hlams
  have hchain : ENNReal.ofReal ((1 / 4 : ℝ) * (1 / 1024 : ℝ) ^ (d ^ 4)) *
      euclideanUnitBallVolume (d ^ 4) ^ 2 * ENNReal.ofReal s ^ (d ^ 4) * unitaryHaar (Fin d × Fin d) S ≤
      ENNReal.ofReal (CV ^ (P + 4 * d ^ 4)) * euclideanUnitBallVolume (d ^ 4) ^ 2 *
        ENNReal.ofReal (s ^ (d ^ 4) * ((Λ' + 2 * s) ^ ℓ * 9 ^ (d ^ 4) * s ^ (d ^ 4 - ℓ))) := by
    refine hlow.trans (hup.trans ?_)
    have hexp : P + 2 * d ^ 4 + 2 * d ^ 4 = P + 4 * d ^ 4 := by omega
    have hcv : max 4 (R + 1 + 1) *
        (((2 * Δ + 1) * ((2 * Δ + 2) * 2 ^ (2 * (c + 1) + 1)) : ℕ) : ℝ) = CV := rfl
    rw [hexp, hcv]
    exact mul_le_mul (mul_le_mul_right (euclideanUnitBallVolume_twice_le_sq (d ^ 4)) _)
      (ENNReal.ofReal_le_ofReal hJ) zero_le zero_le
  have hcancel := cancel_strong_tube_volume hs (by positivity) (pow_nonneg hCV0 _) hchain
  refine hcancel.trans (ENNReal.ofReal_le_ofReal ?_)
  set X := Λ' + 2 * s
  have hX : 0 ≤ X := by positivity
  have hX3 : X ≤ Λ + 3 * s := by simp only [X, hΛ']; linarith
  have hinv : ((1 / 4 : ℝ) * (1 / 1024 : ℝ) ^ (d ^ 4))⁻¹ = 4 * 1024 ^ (d ^ 4) := by
    simp only [one_div, mul_inv, inv_pow, inv_inv]
  calc CV ^ (P + 4 * d ^ 4) * (X ^ ℓ * 9 ^ (d ^ 4) * s ^ (d ^ 4 - ℓ)) / ((1 / 4 : ℝ) * (1 / 1024 : ℝ) ^ (d ^ 4))
      = (4 * 1024 ^ (d ^ 4) * 9 ^ (d ^ 4) * CV ^ (P + 4 * d ^ 4)) * (X ^ ℓ * s ^ (d ^ 4 - ℓ)) := by
        rw [div_eq_mul_inv, hinv]; ring
    _ ≤ Real.exp ((36864 * CV ^ 4) * ((P : ℝ) + ((d ^ 4 : ℕ) : ℝ))) * (X ^ ℓ * s ^ (d ^ 4 - ℓ)) :=
        mul_le_mul_of_nonneg_right (strong_fixed_base_le_exp hCV1 P (d ^ 4) hN1) (by positivity)
    _ ≤ Real.exp ((36864 * CV ^ 4) * ((P : ℝ) + ((d ^ 4 : ℕ) : ℝ))) *
          ((Λ + 3 * s) ^ ℓ * s ^ (d ^ 4 - ℓ)) := by
        gcongr
    _ = _ := by push_cast; ring

/-- **`prop:tube`, displayed form.** For a format budget `(c, Δ)` and radius `R` there is
`C ≥ 1` with `μ(S) ≤ e^{C(P+N)} [C(Λ + s)]^ℓ (C s)^{N-ℓ}` under the hypotheses of
`polynomial_tube_haar_le`. -/
theorem exists_polynomial_tube_constant (c Δ : ℕ) (hΔ : 2 ≤ Δ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d P : ℕ), 2 ≤ d → ∀ (F : PolyFormat P c Δ),
      F.source ⊆ closedBall 0 R → ∀ (T : PolyMap P (2 * d ^ 4) Δ) (ℓ : ℕ), ℓ ≤ d ^ 4 →
      ∀ Λ lam : ℝ, 0 ≤ Λ → 0 ≤ lam →
      (∀ x ∈ F.source, ∃ A B : RealEuclidean P →L[ℝ] RealEuclidean (2 * d ^ 4),
        fderiv ℝ T.eval x = A + B ∧ Module.finrank ℝ (LinearMap.range A.toLinearMap) ≤ ℓ ∧
        ‖fderiv ℝ T.eval x‖ ≤ Λ ∧ ‖B‖ ≤ lam) →
      ∀ τ s : ℝ, 0 ≤ τ → 0 < s → s ≤ 1 / 64 → τ + lam ≤ s →
      ∀ S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ), MeasurableSet S →
      (∀ U ∈ S, ∃ x ∈ F.source,
        dist (normalizedOutputCoordinates d (U : Matrix _ _ ℂ)) (T.eval x) ≤ τ) →
      unitaryHaar (Fin d × Fin d) S ≤
        ENNReal.ofReal (Real.exp (C * ((P : ℝ) + d ^ 4)) * (C * (Λ + s)) ^ ℓ *
          (C * s) ^ (d ^ 4 - ℓ)) := by
  set C0 := 36864 * tubeVolumeConstant c Δ R ^ 4
  have hC0 : 1 ≤ C0 := by
    have := one_le_pow₀ (n := 4) (one_le_tubeVolumeConstant c Δ R)
    simp only [C0]; nlinarith
  refine ⟨max 3 C0, le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro d P hd F h3 T ℓ hℓ Λ lam hΛ hlam hsplit τ s hτ hs hs' hτs S hS hcover
  refine (polynomial_tube_haar_le hd hΔ hR F h3 T hℓ hΛ hlam hsplit hτ hs hs' hτs hS hcover).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hC3 : (3 : ℝ) ≤ max 3 C0 := le_max_left _ _
  have hCC : C0 ≤ max 3 C0 := le_max_right _ _
  have hPN : (0 : ℝ) ≤ (P : ℝ) + d ^ 4 := by positivity
  have h1 : (Λ + 3 * s) ^ ℓ ≤ (max 3 C0 * (Λ + s)) ^ ℓ :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) _
  have h2 : s ^ (d ^ 4 - ℓ) ≤ (max 3 C0 * s) ^ (d ^ 4 - ℓ) :=
    pow_le_pow_left₀ hs.le (by nlinarith) _
  have he : Real.exp (C0 * ((P : ℝ) + d ^ 4)) ≤ Real.exp (max 3 C0 * ((P : ℝ) + d ^ 4)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCC hPN)
  calc Real.exp (C0 * ((P : ℝ) + d ^ 4)) * (Λ + 3 * s) ^ ℓ * s ^ (d ^ 4 - ℓ)
      ≤ Real.exp (max 3 C0 * ((P : ℝ) + d ^ 4)) * (max 3 C0 * (Λ + s)) ^ ℓ *
          (max 3 C0 * s) ^ (d ^ 4 - ℓ) := by gcongr

end DirectVolume

end NLQCLean

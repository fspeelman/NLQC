/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.ImageVolume.LagrangeCharts
import NLQCLean.Geometry.VectorSard
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Image volume of a polynomial map on a barrier domain

Let `U` be an open set with compact closure-like superset `K`, on which a polynomial `φ` is
positive exactly on `U`. For a polynomial map `p : ℝ^a → ℝ^m` whose top Jacobian is at most
`B` on `U`, the image `p(U)` has volume at most

  `B · 2^a · (2D + 2)^(a + m) · vol {z ∈ ℝ^m | ‖z‖ ≤ R}`,

where `D` bounds the degrees of `p` and `φ`, and `U` lies in the ball of radius `R`.

For each `ℓ ∈ [0,1]^a` and each regular value `y ∈ p(U)`, the function `φ · exp⟨ℓ, ·⟩`
attains its maximum on `K ∩ p⁻¹(y)` at a point of `U`. Lagrange multipliers produce
`(x, λ)` with `piMap (x, λ) = (ℓ, y)`. Critical values are null by Sard's theorem. The
change-of-variables inequality for `piMap`, the determinant comparison with the coordinate
charts, and the multiplicity bound for each chart then give the estimate.
-/

namespace NLQCLean
namespace LagrangeCharts

open MvPolynomial MeasureTheory Set Filter
open scoped ENNReal Topology

variable {a m : ℕ}

/-- The set `{(ℓ, y) | ℓ ∈ A, y ∈ B}` in Lagrange coordinates. -/
def blockSet (A : Set (Fin a → ℝ)) (B : Set (Fin m → ℝ)) : Set (Idx a m → ℝ) :=
  {v | (fun j => v (Sum.inl j)) ∈ A ∧ (fun k => v (Sum.inr k)) ∈ B}

theorem volume_blockSet (A : Set (Fin a → ℝ)) (B : Set (Fin m → ℝ)) :
    volume (blockSet A B) = volume A * volume B := by
  have he := volume_measurePreserving_sumPiEquivProdPi (fun _ : Idx a m => ℝ)
  have hpre : blockSet A B =
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Idx a m => ℝ)) ⁻¹' (A ×ˢ B) := by
    ext v
    rfl
  rw [hpre, he.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod]

/-- **Selection by a barrier.** Every regular value of `p` on `U` and every `ℓ` is attained
by the Lagrange map together with `p`. -/
theorem exists_lagrange_point (p : Fin m → MvPolynomial (Fin a) ℝ) (φ : MvPolynomial (Fin a) ℝ)
    {U K : Set (Fin a → ℝ)} (hU : IsOpen U) (hK : IsCompact K) (hUK : U ⊆ K)
    (hφU : ∀ x ∈ U, 0 < eval x φ) (hφK : ∀ x ∈ K, 0 < eval x φ → x ∈ U)
    (ℓ : Fin a → ℝ) {x0 : Fin a → ℝ} (hx0 : x0 ∈ U)
    (hreg : ∀ x ∈ U, polyMap p x = polyMap p x0 →
      Function.Surjective (fderiv ℝ (polyMap p) x)) :
    ∃ w : Idx a m → ℝ, xPart w ∈ U ∧ (∀ j, lagrangeMap p φ j w = ℓ j) ∧
      polyMap p (xPart w) = polyMap p x0 := by
  classical
  set y := polyMap p x0 with hy
  let Lℓ : (Fin a → ℝ) →L[ℝ] ℝ := ∑ j, ℓ j • ContinuousLinearMap.proj j
  have hLℓ : ∀ x, Lℓ x = ∑ j, ℓ j * x j := by
    intro x
    simp [Lℓ]
  let χ : (Fin a → ℝ) → ℝ := fun x => eval x φ * Real.exp (Lℓ x)
  have hχC1 : ContDiff ℝ 1 χ :=
    (contDiff_eval_pi φ).mul (Real.contDiff_exp.comp Lℓ.contDiff)
  set Ky := K ∩ polyMap p ⁻¹' {y}
  have hKy : IsCompact Ky :=
    hK.inter_right (isClosed_singleton.preimage (contDiff_polyMap (n := 0) p).continuous)
  have hx0K : x0 ∈ Ky := ⟨hUK hx0, rfl⟩
  obtain ⟨xs, hxsK, hmax⟩ := hKy.exists_isMaxOn ⟨x0, hx0K⟩ hχC1.continuous.continuousOn
  have hχx0 : 0 < χ x0 := mul_pos (hφU x0 hx0) (Real.exp_pos _)
  have hφxs : 0 < eval xs φ := by
    have h : χ x0 ≤ χ xs := hmax hx0K
    have hχxs : χ xs = eval xs φ * Real.exp (Lℓ xs) := rfl
    by_contra hneg
    push Not at hneg
    nlinarith [Real.exp_pos (Lℓ xs)]
  have hxsU : xs ∈ U := hφK xs hxsK.1 hφxs
  have hyxs : polyMap p xs = y := hxsK.2
  have hloc : IsLocalMaxOn χ {x | polyMap p x = polyMap p xs} xs := by
    change ∀ᶠ x in 𝓝[{x | polyMap p x = polyMap p xs}] xs, χ x ≤ χ xs
    filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hxsU), self_mem_nhdsWithin] with x hxU hx
    exact hmax ⟨hUK hxU, by
      change polyMap p x = y
      rw [← hyxs]
      exact hx⟩
  have hpd : HasStrictFDerivAt (polyMap p) (fderiv ℝ (polyMap p) xs) xs :=
    (contDiff_polyMap (n := 1) p).contDiffAt.hasStrictFDerivAt one_ne_zero
  have hχd : HasStrictFDerivAt χ (fderiv ℝ χ xs) xs :=
    hχC1.contDiffAt.hasStrictFDerivAt one_ne_zero
  have hextr : IsLocalExtrOn χ {x | polyMap p x = polyMap p xs} xs := Or.inr hloc
  obtain ⟨Λ, Λ₀, hne, hΛ⟩ := hextr.exists_linear_map_of_hasStrictFDerivAt hpd hχd
  have hsurj := hreg xs hxsU hyxs
  have hΛ₀ : Λ₀ ≠ 0 := by
    intro h0
    apply hne
    have hΛz : Λ = 0 := by
      refine LinearMap.ext fun v => ?_
      obtain ⟨h, rfl⟩ := hsurj v
      have := hΛ h
      rw [h0, zero_smul, add_zero] at this
      simpa using this
    rw [hΛz, h0]
    rfl
  have hEne : Real.exp (Lℓ xs) ≠ 0 := (Real.exp_pos _).ne'
  have hφne : eval xs φ ≠ 0 := hφxs.ne'
  have hχval : ∀ j, fderiv ℝ χ xs (Pi.single j 1) =
      Real.exp (Lℓ xs) * (eval xs (pderiv j φ) + eval xs φ * ℓ j) := by
    have hd : HasFDerivAt χ
        (eval xs φ • (Real.exp (Lℓ xs) • Lℓ) + Real.exp (Lℓ xs) • polyGradient φ xs) xs :=
      (hasFDerivAt_eval_pi φ xs).fun_mul (Lℓ.hasFDerivAt.exp)
    intro j
    rw [hd.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul,
      polyGradient_single, hLℓ, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  have hΛexp : ∀ j, Λ (fderiv ℝ (polyMap p) xs (Pi.single j 1)) =
      ∑ k, eval xs (pderiv j (p k)) * Λ (Pi.single k 1) := by
    intro j
    rw [LinearMap.pi_apply_eq_sum_univ Λ]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [fderiv_polyMap_single, smul_eq_mul, single_eq_ite']
  let lam : Fin m → ℝ := fun k =>
    -(Λ (Pi.single k 1)) / (Λ₀ * (Real.exp (Lℓ xs) * eval xs φ))
  refine ⟨Sum.elim xs lam, hxsU, fun j => ?_, hyxs.trans hy⟩
  have hj := hΛ (Pi.single j 1)
  rw [hΛexp, smul_eq_mul, hχval] at hj
  have hx : xPart (Sum.elim xs lam : Idx a m → ℝ) = xs := rfl
  rw [lagrangeMap, eval_lagrangeNum, hx, div_eq_iff hφne]
  simp only [Sum.elim_inr, lam]
  have hsum : ∑ k, -(Λ (Pi.single k 1)) / (Λ₀ * (Real.exp (Lℓ xs) * eval xs φ)) *
        eval xs (pderiv j (p k)) =
      -(∑ k, eval xs (pderiv j (p k)) * Λ (Pi.single k 1)) /
        (Λ₀ * (Real.exp (Lℓ xs) * eval xs φ)) := by
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hsum]
  have hj' : ∑ k, eval xs (pderiv j (p k)) * Λ (Pi.single k 1) =
      -(Λ₀ * (Real.exp (Lℓ xs) * (eval xs (pderiv j φ) + eval xs φ * ℓ j))) := by
    linarith
  rw [hj']
  field_simp
  ring

/-- **Image volume on a barrier domain.** -/
theorem volume_polyMap_image_le {D : ℕ} (p : Fin m → MvPolynomial (Fin a) ℝ)
    (φ : MvPolynomial (Fin a) ℝ) (hp : ∀ k, (p k).totalDegree ≤ D) (hφ : φ.totalDegree ≤ D)
    {U K : Set (Fin a → ℝ)} (hU : IsOpen U) (hK : IsCompact K) (hUK : U ⊆ K)
    (hφU : ∀ x ∈ U, 0 < eval x φ) (hφK : ∀ x ∈ K, 0 < eval x φ → x ∈ U)
    {R : ℝ} (hUR : ∀ x ∈ U, ∑ i, x i ^ 2 ≤ R ^ 2)
    {B : ℝ} (hB : 0 ≤ B) (hJ : ∀ x ∈ U, gradJacobian p x ≤ B) :
    volume (polyMap p '' U) ≤ ENNReal.ofReal B * ((2 ^ a * (2 * D + 2) ^ (a + m) : ℕ) : ℝ≥0∞) *
      volume {z : Fin m → ℝ | ∑ k, z k ^ 2 ≤ R ^ 2} := by
  classical
  set N : ℕ := (2 * D + 2) ^ (a + m)
  set Q : Set (Fin a → ℝ) := Icc 0 1
  set Z : Set (Fin m → ℝ) := {z | ∑ k, z k ^ 2 ≤ R ^ 2}
  set Crit : Set (Fin a → ℝ) := {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ (polyMap p) x)}
  set Y := polyMap p '' U \ polyMap p '' Crit
  set E : Set (Idx a m → ℝ) := {w | xPart w ∈ U ∧ (fun j => lagrangeMap p φ j w) ∈ Q}
  have hφE : ∀ w ∈ E, eval (xPart w) φ ≠ 0 := fun w hw => (hφU _ hw.1).ne'
  have hEmeas : MeasurableSet E := by
    refine (hU.preimage continuous_xPart).measurableSet.inter ?_
    exact measurableSet_Icc.preimage (Measurable.of_eval fun j => measurable_lagrangeMap p φ j)
  have hsard : volume (polyMap p '' Crit) = 0 :=
    criticalImage_volume_eq_zero (contDiff_polyMap p) fun x hx => hx.2
  have h1 : volume (polyMap p '' U) ≤ volume Y := by
    calc volume (polyMap p '' U) ≤ volume (Y ∪ polyMap p '' Crit) := by
          refine measure_mono fun y hy => ?_
          by_cases h : y ∈ polyMap p '' Crit
          · exact Or.inr h
          · exact Or.inl ⟨hy, h⟩
      _ ≤ volume Y + volume (polyMap p '' Crit) := measure_union_le _ _
      _ = volume Y := by rw [hsard, add_zero]
  have h2 : blockSet Q Y ⊆ piMap p φ '' E := by
    rintro v ⟨hvQ, hvY⟩
    obtain ⟨⟨x0, hx0, hx0y⟩, hncrit⟩ := hvY
    have hreg : ∀ x ∈ U, polyMap p x = polyMap p x0 →
        Function.Surjective (fderiv ℝ (polyMap p) x) := by
      intro x hx hxy
      by_contra hns
      exact hncrit ⟨x, ⟨hx, hns⟩, hxy.trans hx0y⟩
    obtain ⟨w, hwU, hwΦ, hwp⟩ := exists_lagrange_point p φ hU hK hUK hφU hφK
      (fun j => v (Sum.inl j)) hx0 hreg
    have hfun : (fun j => lagrangeMap p φ j w) = fun j => v (Sum.inl j) := funext hwΦ
    refine ⟨w, ⟨hwU, by rw [hfun]; exact hvQ⟩, ?_⟩
    funext r
    rcases r with j | k
    · exact hwΦ j
    · have h := congrFun (hwp.trans hx0y) k
      exact h
  have hQ : volume Q = 1 := by
    simp [Q, Real.volume_Icc_pi]
  have h3 : volume Y = volume (blockSet Q Y) := by
    rw [volume_blockSet, hQ, one_mul]
  have hderivE : ∀ w ∈ E, HasFDerivWithinAt (piMap p φ) (fderiv ℝ (piMap p φ) w) E w :=
    fun w hw => ((contDiffAt_piMap (n := 1) p φ (hφE w hw)).differentiableAt
      one_ne_zero).hasFDerivAt.hasFDerivWithinAt
  have h4 : volume (piMap p φ '' E) ≤
      ∫⁻ w in E, ENNReal.ofReal |(fderiv ℝ (piMap p φ) w).det| :=
    addHaar_image_le_lintegral_abs_det_fderiv volume hEmeas hderivE
  have h5 : ∫⁻ w in E, ENNReal.ofReal |(fderiv ℝ (piMap p φ) w).det| ≤
      ∫⁻ w in E, ENNReal.ofReal B *
        ∑ s : Set.powersetCard (Fin a) m, ENNReal.ofReal |(fderiv ℝ (chartMap p φ s) w).det| := by
    refine setLIntegral_mono' hEmeas fun w hw => ?_
    have hdet := abs_det_fderiv_piMap_le p φ (hφE w hw)
    have hJw := hJ _ hw.1
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => abs_nonneg _), ← ENNReal.ofReal_mul hB]
    exact ENNReal.ofReal_le_ofReal (hdet.trans
      (mul_le_mul_of_nonneg_right hJw (Finset.sum_nonneg fun s _ => abs_nonneg _)))
  have hmeasdet : ∀ s : Set.powersetCard (Fin a) m,
      Measurable fun w : Idx a m → ℝ => (fderiv ℝ (chartMap p φ s) w).det := fun s =>
    ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ _)
  have h6 : ∫⁻ w in E, ENNReal.ofReal B *
        ∑ s : Set.powersetCard (Fin a) m, ENNReal.ofReal |(fderiv ℝ (chartMap p φ s) w).det| =
      ENNReal.ofReal B * ∑ s : Set.powersetCard (Fin a) m,
        ∫⁻ w in E, ENNReal.ofReal |(fderiv ℝ (chartMap p φ s) w).det| := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum']
    intro s _
    exact (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      (hmeasdet s))).aemeasurable
  have hZ : volume (blockSet Q Z) = volume Z := by
    rw [volume_blockSet, hQ, one_mul]
  have h7 : ∀ s : Set.powersetCard (Fin a) m,
      ∫⁻ w in E, ENNReal.ofReal |(fderiv ℝ (chartMap p φ s) w).det| ≤ (N : ℝ≥0∞) * volume Z := by
    intro s
    set S := {w : Idx a m → ℝ | (fderiv ℝ (chartMap p φ s) w).det ≠ 0}
    have hSmeas : MeasurableSet S :=
      (measurableSet_singleton (0 : ℝ)).compl.preimage (hmeasdet s)
    have hE'meas : MeasurableSet (E ∩ S) := hEmeas.inter hSmeas
    have hsplit : ∫⁻ w in E, ENNReal.ofReal |(fderiv ℝ (chartMap p φ s) w).det| =
        ∫⁻ w in E ∩ S, ENNReal.ofReal |(fderiv ℝ (chartMap p φ s) w).det| := by
      rw [← lintegral_inter_add_sdiff _ E hSmeas]
      have hz : ∫⁻ w in E \ S, ENNReal.ofReal |(fderiv ℝ (chartMap p φ s) w).det| = 0 := by
        refine setLIntegral_eq_zero (hEmeas.diff hSmeas) fun w hw => ?_
        have : (fderiv ℝ (chartMap p φ s) w).det = 0 := by
          by_contra h
          exact hw.2 h
        simp [this]
      rw [hz, add_zero]
    rw [hsplit]
    have himage : chartMap p φ s '' (E ∩ S) ⊆ blockSet Q Z := by
      rintro _ ⟨w, ⟨⟨hwU, hwQ⟩, -⟩, rfl⟩
      refine ⟨hwQ, ?_⟩
      change ∑ k, (w (Sum.inl (coordinateMinorAxes s k))) ^ 2 ≤ R ^ 2
      refine le_trans ?_ (hUR _ hwU)
      have hinj := coordinateMinorAxes_injective s
      calc ∑ k, (w (Sum.inl (coordinateMinorAxes s k))) ^ 2
          = ∑ i ∈ Finset.univ.image (coordinateMinorAxes s), (xPart w i) ^ 2 := by
            rw [Finset.sum_image fun x _ y _ h => hinj h]
            rfl
        _ ≤ ∑ i, (xPart w i) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              fun i _ _ => sq_nonneg _
    calc ∫⁻ w in E ∩ S, ENNReal.ofReal |(fderiv ℝ (chartMap p φ s) w).det|
        ≤ (N : ℝ≥0∞) * volume (chartMap p φ s '' (E ∩ S)) :=
          lintegral_abs_det_le_mul_addHaar_image volume hE'meas
            (fun w hw => (contDiffAt_chartMap (n := 1) p φ s (hφE w hw.1)).hasStrictFDerivAt
              one_ne_zero)
            (fun w hw => hw.2) N
            (fun y T hT => card_regular_fiber_le p φ hp hφ s y T fun w hw =>
              ⟨⟨hφE w (hT w hw).1.1, (hT w hw).1.2⟩, (hT w hw).2⟩)
      _ ≤ (N : ℝ≥0∞) * volume (blockSet Q Z) := by gcongr
      _ = (N : ℝ≥0∞) * volume Z := by rw [hZ]
  have hcard : (Fintype.card (Set.powersetCard (Fin a) m) : ℝ≥0∞) ≤ 2 ^ a := by
    exact_mod_cast card_coordinateMinorIndices_le a m
  calc volume (polyMap p '' U) ≤ volume (blockSet Q Y) := h1.trans h3.le
    _ ≤ volume (piMap p φ '' E) := measure_mono h2
    _ ≤ _ := h4
    _ ≤ _ := h5
    _ = _ := h6
    _ ≤ ENNReal.ofReal B * ∑ _s : Set.powersetCard (Fin a) m, (N : ℝ≥0∞) * volume Z := by
        gcongr with s
        exact h7 s
    _ = ENNReal.ofReal B * ((Fintype.card (Set.powersetCard (Fin a) m) : ℝ≥0∞) *
          ((N : ℝ≥0∞) * volume Z)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal B * (2 ^ a * ((N : ℝ≥0∞) * volume Z)) := by gcongr
    _ = ENNReal.ofReal B * ((2 ^ a * N : ℕ) : ℝ≥0∞) * volume Z := by
        push_cast
        ring

end LagrangeCharts
end NLQCLean

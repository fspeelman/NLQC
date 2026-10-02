import NLQCLean.Geometry.DirectVolume.Charts
import NLQCLean.Geometry.SemialgebraicImageVolume
import NLQCLean.Geometry.JacobianNeighborhood

/-!
# Direct image-volume route: assembly

`PolynomialImageVolumeBound` with the constant `804 · 560 = 450240` and **no
external hypothesis**: no LRT selections, no smooth stratification and no component
bound.

For fixed `η > 0`: perturb the source outward to a compact level source `S_b`
on which the top Jacobian is below `B + η` (L1); choose the level vector `b`
and the direction `v` jointly outside a null set (§11 of `D0-PROOF.md`); cover
`p(S_b)` by null singular values and the images of the Lagrange sets of the
strata `J ⊆ Fin 41` (L6); bound each such image by the C¹-piece volume engine with
the fiber count `201^(a+m+|J|)` (L11, L15); then let `η → 0`. A stratum with
`m + |J| > a` has no point with independent gradients, so its Lagrange set is
empty, and the remaining count `Σ_{|J| ≤ a-m} 201^|J|` grows only like `560^(a-m)`.
Roadmap step D7.
-/

namespace NLQCLean.DirectVolume

open MvPolynomial Set Function Filter Topology MeasureTheory Metric
open scoped ENNReal

variable {a m : ℕ}

/-- Parameters `(b, v)` outside all the exceptional null sets. -/
def GoodLagrangeParameters (p : BoundedPolynomialMap a m)
    (g : Fin 41 → MvPolynomial (Fin a) ℝ) (b : Fin 41 → ℝ) (v : Fin a → ℝ) : Prop :=
  (∀ J, volume (singularLevelValues p g J b) = 0) ∧
  (∀ J q, lagrangeMap p g J q = (b, v) → Surjective (fderiv ℝ (lagrangeMap p g J) q)) ∧
  (∀ J (I : Fin m → Fin a), ∀ᵐ z, ∀ q, lagrangeCoordMap p g J I q = ((b, v), z) →
    Surjective (fderiv ℝ (lagrangeCoordMap p g J I) q))

theorem ae_goodLagrangeParameters (p : BoundedPolynomialMap a m)
    (g : Fin 41 → MvPolynomial (Fin a) ℝ) :
    ∀ᵐ bv : (Fin 41 → ℝ) × (Fin a → ℝ), GoodLagrangeParameters p g bv.1 bv.2 := by
  have h1 : ∀ᵐ bv : (Fin 41 → ℝ) × (Fin a → ℝ),
      ∀ J, volume (singularLevelValues p g J bv.1) = 0 := by
    rw [ae_all_iff]
    intro J
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_fst.ae (ae_volume_singularLevelValues p g J)
  have h2 : ∀ᵐ bv : (Fin 41 → ℝ) × (Fin a → ℝ), ∀ J q, lagrangeMap p g J q = bv →
      Surjective (fderiv ℝ (lagrangeMap p g J) q) := by
    rw [ae_all_iff]
    exact fun J => ae_regular_lagrangeMap p g J
  have h3 : ∀ᵐ bv : (Fin 41 → ℝ) × (Fin a → ℝ), ∀ J (I : Fin m → Fin a), ∀ᵐ z, ∀ q,
      lagrangeCoordMap p g J I q = (bv, z) →
        Surjective (fderiv ℝ (lagrangeCoordMap p g J I) q) := by
    rw [ae_all_iff]
    intro J
    rw [ae_all_iff]
    exact fun I => ae_ae_regular_lagrangeCoordMap p g J I
  filter_upwards [h1, h2, h3] with bv hb1 hb2 hb3
  exact ⟨hb1, hb2, hb3⟩

/-- Good parameters with levels in `(-δ, 0)`. -/
theorem exists_goodLagrangeParameters (p : BoundedPolynomialMap a m)
    (g : Fin 41 → MvPolynomial (Fin a) ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : Fin 41 → ℝ, ∃ v : Fin a → ℝ, (∀ t, -δ < b t ∧ b t ≤ 0) ∧
      GoodLagrangeParameters p g b v := by
  set box : Set ((Fin 41 → ℝ) × (Fin a → ℝ)) := (Set.univ.pi fun _ => Ioo (-δ) 0) ×ˢ univ
  have hbox : volume box ≠ 0 := by
    have := isAddHaarMeasure_volume_pi (Fin a)
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_pi_Ioo]
    refine mul_ne_zero ?_ (isOpen_univ.measure_ne_zero volume univ_nonempty)
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => by simp [hδ]
  obtain ⟨⟨b, v⟩, ⟨hb, -⟩, hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hbox
    (ae_restrict_of_ae (ae_goodLagrangeParameters p g))
  exact ⟨b, v, fun t => ⟨(hb t (mem_univ t)).1, (hb t (mem_univ t)).2.le⟩, hgood⟩

/-- The fiber count of a stratum, zero when `m + |J| > a`. -/
def stratumCount (a m : ℕ) (J : Finset (Fin 41)) : ℕ :=
  if m + J.card ≤ a then 201 ^ (a + m + J.card) else 0

/-- **L16 (one stratum).** -/
theorem volume_image_lagrangeSet_le (p : BoundedPolynomialMap a m)
    (g : Fin 41 → MvPolynomial (Fin a) ℝ) (hg : ∀ t, (g t).totalDegree ≤ 100)
    {b : Fin 41 → ℝ} {v : Fin a → ℝ} (hgood : GoodLagrangeParameters p g b v)
    (hball : levelSource g b ⊆ closedBall 0 4) {B' : ℝ} (hB' : 0 ≤ B')
    (hJ : ∀ x ∈ levelSource g b, topRealJacobian (fderiv ℝ p.eval x) ≤ B')
    (J : Finset (Fin 41)) :
    volume (p.eval '' lagrangeSet p g J b v) ≤
      ENNReal.ofReal ((4 : ℝ) ^ a) * (stratumCount a m J : ℝ≥0∞) *
        euclideanUnitBallVolume m * ENNReal.ofReal ((4 : ℝ) ^ m) * ENNReal.ofReal B' := by
  by_cases hne : (lagrangeLevel p g J b v).Nonempty
  · have hmJ : m + J.card ≤ a := by
      obtain ⟨q, -, hq, -⟩ := hne
      simpa [Fintype.card_sum] using hq.fintype_card_le_finrank
    rw [stratumCount, ite_eq_left hmJ]
    obtain ⟨φ, D, hDm, hDcube, hφ, hinj, hder, hdis, hcover⟩ :=
      exists_lagrangeCharts p g J b v (hgood.2.1 J) hne
    have hsub := lagrangeSet_subset_levelSource p g J b v
    have hvol := volume_iUnion_C1Pieces_le φ D hDm hDcube hφ hinj hder hdis
      (lagrangeSet p g J b v) (fun n => hcover ▸ subset_iUnion (fun n => φ n '' D n) n)
      (hsub.trans hball) (201 ^ (a + m + J.card))
      (fun I _ => by
        filter_upwards [hgood.2.2 J I] with z hz
        exact lagrangeSet_coordinateFiber_finite_card_le p g hg J I b v z hz)
      p.eval isOpen_univ (subset_univ _) p.contDiff_eval.contDiffOn hB'
      (fun x hx => hJ x (hsub hx))
    rw [hcover] at hvol
    exact hvol.trans_eq (coordinate_graph_volume_constant_eq a m _ (by norm_num) hB')
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hempty : lagrangeSet p g J b v = ∅ := by
      simp only [lagrangeSet, hne, Set.image_empty]
    rw [hempty, Set.image_empty, measure_empty]
    exact zero_le

/-- The strata with `|J| ≤ n` weighted by `201^|J|`: by
`Σ_J 201^|J| 560^(41-|J|) = 761⁴¹ ≤ 560⁴³` the sum is at most `560^(n+2)`. -/
theorem sum_stratumWeight_le (n : ℕ) :
    ∑ J : Finset (Fin 41), (if J.card ≤ n then 201 ^ J.card else 0) ≤ 560 ^ (n + 2) := by
  have key : ∀ J : Finset (Fin 41), (if J.card ≤ n then 201 ^ J.card else 0) * 560 ^ 41 ≤
      560 ^ n * (201 ^ J.card * 560 ^ (41 - J.card)) := by
    intro J
    split_ifs with h
    · have hJ : J.card ≤ 41 := by simpa using J.card_le_univ
      calc 201 ^ J.card * 560 ^ 41
          = 201 ^ J.card * (560 ^ J.card * 560 ^ (41 - J.card)) := by
            rw [← pow_add, Nat.add_sub_cancel' hJ]
        _ ≤ 201 ^ J.card * (560 ^ n * 560 ^ (41 - J.card)) := by
            gcongr
        _ = 560 ^ n * (201 ^ J.card * 560 ^ (41 - J.card)) := by ring
    · simp
  have hsum : (∑ J : Finset (Fin 41), (if J.card ≤ n then 201 ^ J.card else 0)) * 560 ^ 41 ≤
      560 ^ n * 761 ^ 41 := by
    have hbin := Fintype.sum_pow_mul_eq_add_pow (Fin 41) (201 : ℕ) 560
    rw [Fintype.card_fin] at hbin
    calc _ = ∑ J : Finset (Fin 41), (if J.card ≤ n then 201 ^ J.card else 0) * 560 ^ 41 :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ J : Finset (Fin 41), 560 ^ n * (201 ^ J.card * 560 ^ (41 - J.card)) :=
          Finset.sum_le_sum fun J _ => key J
      _ = 560 ^ n * 761 ^ 41 := by rw [← Finset.mul_sum, hbin]
  refine Nat.le_of_mul_le_mul_right ?_ (by positivity : 0 < 560 ^ 41)
  calc _ ≤ 560 ^ n * 761 ^ 41 := hsum
    _ ≤ 560 ^ n * 560 ^ 43 := Nat.mul_le_mul_left _ (by decide)
    _ = 560 ^ (n + 2) * 560 ^ 41 := by ring

/-- The constant `804 · 560` absorbs `4^a · Σ_J stratumCount · 4^m`. -/
theorem sum_stratumCount_le {a m : ℕ} (hm : 1 ≤ m) :
    4 ^ a * (∑ J : Finset (Fin 41), stratumCount a m J) * 4 ^ m ≤ (804 * 560) ^ (a + m) := by
  by_cases ham : m ≤ a
  · obtain ⟨n, rfl⟩ : ∃ n, a = m + n := ⟨a - m, by omega⟩
    have hcount : ∀ J : Finset (Fin 41), stratumCount (m + n) m J =
        201 ^ (m + n + m) * (if J.card ≤ n then 201 ^ J.card else 0) := by
      intro J
      unfold stratumCount
      by_cases h : J.card ≤ n
      · rw [ite_eq_left (by omega), ite_eq_left h, pow_add]
      · rw [ite_eq_right (by omega), ite_eq_right h, mul_zero]
    simp_rw [hcount, ← Finset.mul_sum]
    calc _ ≤ 4 ^ (m + n) * (201 ^ (m + n + m) * 560 ^ (n + 2)) * 4 ^ m := by
          gcongr; exact sum_stratumWeight_le n
      _ ≤ 4 ^ (m + n) * (201 ^ (m + n + m) * 560 ^ (m + n + m)) * 4 ^ m := by
          have h560 : 560 ^ (n + 2) ≤ 560 ^ (m + n + m) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          gcongr
      _ = (4 * 201 * 560) ^ (m + n + m) := by rw [mul_pow, mul_pow]; ring
      _ = _ := by norm_num
  · have h0 : ∀ J : Finset (Fin 41), stratumCount a m J = 0 := fun J => by
      unfold stratumCount; rw [ite_eq_right (by omega)]
    simp [h0]

/-- The bound for a fixed `η > 0`. -/
theorem volume_image_le_add (F : PolynomialBasicClosedFormat a) (p : BoundedPolynomialMap a m)
    (hm : 1 ≤ m) (h3 : F.source ⊆ closedBall 0 3) {B : ℝ} (hB : 0 ≤ B)
    (hJ : ∀ x ∈ F.source, topRealJacobian (fderiv ℝ p.eval x) ≤ B) {η : ℝ} (hη : 0 < η) :
    volume (p.eval '' F.source) ≤
      ENNReal.ofReal (((804 : ℝ) * 560) ^ (a + m)) * euclideanUnitBallVolume m *
        ENNReal.ofReal (B + η) := by
  classical
  set g := levelPolys F with hg
  set U : Set (RealEuclidean a) := {x | topRealJacobian (fderiv ℝ p.eval x) < B + η} with hU
  have hUo : IsOpen U :=
    isOpen_lt (ContDiff.continuous_topRealJacobian_fderiv p.contDiff_eval) continuous_const
  have hSU : F.source ⊆ U := fun x hx => lt_of_le_of_lt (hJ x hx) (by linarith)
  obtain ⟨δ, hδ, -, hfam⟩ := exists_levelFamily F h3 hUo hSU
  obtain ⟨b, v, hb, hgood⟩ := exists_goodLagrangeParameters p g hδ
  obtain ⟨hSSb, hball, hcpt, hSbU⟩ := hfam b hb
  have hJb : ∀ x ∈ levelSource g b, topRealJacobian (fderiv ℝ p.eval x) ≤ B + η :=
    fun x hx => (hSbU hx).le
  have hstrata : volume (⋃ J : Finset (Fin 41), p.eval '' lagrangeSet p g J b v) ≤
      ((4 ^ a * (∑ J : Finset (Fin 41), stratumCount a m J) * 4 ^ m : ℕ) : ℝ≥0∞) *
        euclideanUnitBallVolume m * ENNReal.ofReal (B + η) := by
    have e4 : ∀ k : ℕ, ENNReal.ofReal ((4 : ℝ) ^ k) = (4 : ℝ≥0∞) ^ k := fun k => by
      rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    calc _ ≤ ∑' J : Finset (Fin 41), volume (p.eval '' lagrangeSet p g J b v) :=
          measure_iUnion_le _
      _ ≤ ∑' J : Finset (Fin 41), ENNReal.ofReal ((4 : ℝ) ^ a) *
            (stratumCount a m J : ℝ≥0∞) * euclideanUnitBallVolume m *
            ENNReal.ofReal ((4 : ℝ) ^ m) * ENNReal.ofReal (B + η) :=
          ENNReal.tsum_le_tsum fun J =>
            volume_image_lagrangeSet_le p g (levelPolys_degree_le F) hgood hball
              (by linarith) hJb J
      _ = _ := by
          rw [tsum_fintype]
          simp only [e4, Nat.cast_mul, Nat.cast_pow, Nat.cast_sum, Nat.cast_ofNat,
            Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun J _ => ?_
          ring
  have hsing : volume (⋃ J : Finset (Fin 41), singularLevelValues p g J b) = 0 :=
    measure_iUnion_null hgood.1
  calc volume (p.eval '' F.source)
      ≤ volume (p.eval '' levelSource g b) := measure_mono (image_mono hSSb)
    _ ≤ volume ((⋃ J : Finset (Fin 41), singularLevelValues p g J b) ∪
          ⋃ J : Finset (Fin 41), p.eval '' lagrangeSet p g J b v) :=
        measure_mono (image_levelSource_subset p g b hcpt v)
    _ ≤ volume (⋃ J : Finset (Fin 41), singularLevelValues p g J b) +
          volume (⋃ J : Finset (Fin 41), p.eval '' lagrangeSet p g J b v) :=
        measure_union_le _ _
    _ ≤ ((4 ^ a * (∑ J : Finset (Fin 41), stratumCount a m J) * 4 ^ m : ℕ) : ℝ≥0∞) *
          euclideanUnitBallVolume m * ENNReal.ofReal (B + η) := by
        rw [hsing, zero_add]; exact hstrata
    _ ≤ _ := by
        gcongr
        rw [← ENNReal.ofReal_natCast]
        gcongr
        exact_mod_cast sum_stratumCount_le hm

theorem euclideanUnitBallVolume_ne_top' (m : ℕ) : euclideanUnitBallVolume m ≠ ∞ :=
  measure_ball_lt_top.ne

/-- **The polynomial image-volume bound with the explicit constant `804 · 560`.** -/
theorem polynomialImageVolumeBoundWith : PolynomialImageVolumeBoundWith (804 * 560) := by
  intro a m _ha hm F p _hF h3 B hB hJ
  have hK : ENNReal.ofReal (((804 : ℝ) * 560) ^ (a + m)) * euclideanUnitBallVolume m ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (euclideanUnitBallVolume_ne_top' m)
  have hlim : Tendsto (fun j : ℕ => ENNReal.ofReal (B + 1 / ((j : ℝ) + 1))) atTop
      (𝓝 (ENNReal.ofReal B)) := by
    have hT : Tendsto (fun j : ℕ => B + 1 / ((j : ℝ) + 1)) atTop (𝓝 B) := by
      simpa only [add_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add B
    simpa only [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto B).comp hT
  exact ge_of_tendsto' (ENNReal.Tendsto.const_mul hlim (Or.inr hK))
    (fun j => volume_image_le_add F p hm h3 hB hJ (by positivity))

/-- **`PolynomialImageVolumeBound` without external hypotheses.** -/
theorem polynomialImageVolumeBound : PolynomialImageVolumeBound :=
  ⟨804 * 560, by norm_num, polynomialImageVolumeBoundWith⟩

end NLQCLean.DirectVolume

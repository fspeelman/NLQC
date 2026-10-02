import NLQCLean.Geometry.DirectVolume.Charts
import NLQCLean.Geometry.SemialgebraicImageVolume
import NLQCLean.Geometry.JacobianNeighborhood

/-!
# Direct image-volume route: assembly

The polynomial image-volume bound for every basic closed polynomial format with at most
`c` constraints of degree at most `Δ ≥ 2` and radius `R`: the constant is
`max(4, R+1) · (2Δ+1) · c'` for any `c' ≥ 1` with `(2Δ+1+c')^(2c+1) ≤ c'^(2c+3)`. For the
contract formats (`c = 20`, `Δ = 100`, `R = 3`, `c' = 560`) this is
`PolynomialImageVolumeBound` with the constant `804 · 560 = 450240`, with **no external
hypothesis**: no LRT selections, no smooth stratification and no component bound.

For fixed `η > 0`: perturb the source outward to a compact level source `S_b`
on which the top Jacobian is below `B + η` (L1); choose the level vector `b`
and the direction `v` jointly outside a null set (§11 of `D0-PROOF.md`); cover
`p(S_b)` by null singular values and the images of the Lagrange sets of the
strata `J ⊆ Fin L` (L6); bound each such image by the C¹-piece volume engine with
the fiber count `201^(a+m+|J|)` (L11, L15); then let `η → 0`. A stratum with
`m + |J| > a` has no point with independent gradients, so its Lagrange set is
empty, and the remaining count `Σ_{|J| ≤ a-m} 201^|J|` grows only like `560^(a-m)`.
Roadmap step D7.
-/

namespace NLQCLean.DirectVolume

open MvPolynomial Set Function Filter Topology MeasureTheory Metric
open scoped ENNReal

variable {a m L D : ℕ}

/-- Parameters `(b, v)` outside all the exceptional null sets. -/
def GoodLagrangeParameters (p : PolyMap a m D)
    (g : Fin L → MvPolynomial (Fin a) ℝ) (b : Fin L → ℝ) (v : Fin a → ℝ) : Prop :=
  (∀ J, volume (singularLevelValues p g J b) = 0) ∧
  (∀ J q, lagrangeMap p g J q = (b, v) → Surjective (fderiv ℝ (lagrangeMap p g J) q)) ∧
  (∀ J (I : Fin m → Fin a), ∀ᵐ z, ∀ q, lagrangeCoordMap p g J I q = ((b, v), z) →
    Surjective (fderiv ℝ (lagrangeCoordMap p g J I) q))

theorem ae_goodLagrangeParameters (p : PolyMap a m D)
    (g : Fin L → MvPolynomial (Fin a) ℝ) :
    ∀ᵐ bv : (Fin L → ℝ) × (Fin a → ℝ), GoodLagrangeParameters p g bv.1 bv.2 := by
  have h1 : ∀ᵐ bv : (Fin L → ℝ) × (Fin a → ℝ),
      ∀ J, volume (singularLevelValues p g J bv.1) = 0 := by
    rw [ae_all_iff]
    intro J
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_fst.ae (ae_volume_singularLevelValues p g J)
  have h2 : ∀ᵐ bv : (Fin L → ℝ) × (Fin a → ℝ), ∀ J q, lagrangeMap p g J q = bv →
      Surjective (fderiv ℝ (lagrangeMap p g J) q) := by
    rw [ae_all_iff]
    exact fun J => ae_regular_lagrangeMap p g J
  have h3 : ∀ᵐ bv : (Fin L → ℝ) × (Fin a → ℝ), ∀ J (I : Fin m → Fin a), ∀ᵐ z, ∀ q,
      lagrangeCoordMap p g J I q = (bv, z) →
        Surjective (fderiv ℝ (lagrangeCoordMap p g J I) q) := by
    rw [ae_all_iff]
    intro J
    rw [ae_all_iff]
    exact fun I => ae_ae_regular_lagrangeCoordMap p g J I
  filter_upwards [h1, h2, h3] with bv hb1 hb2 hb3
  exact ⟨hb1, hb2, hb3⟩

/-- Good parameters with levels in `(-δ, 0)`. -/
theorem exists_goodLagrangeParameters (p : PolyMap a m D)
    (g : Fin L → MvPolynomial (Fin a) ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : Fin L → ℝ, ∃ v : Fin a → ℝ, (∀ t, -δ < b t ∧ b t ≤ 0) ∧
      GoodLagrangeParameters p g b v := by
  set box : Set ((Fin L → ℝ) × (Fin a → ℝ)) := (Set.univ.pi fun _ => Ioo (-δ) 0) ×ˢ univ
  have hbox : volume box ≠ 0 := by
    have := isAddHaarMeasure_volume_pi (Fin a)
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_pi_Ioo]
    refine mul_ne_zero ?_ (isOpen_univ.measure_ne_zero volume univ_nonempty)
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => by simp [hδ]
  obtain ⟨⟨b, v⟩, ⟨hb, -⟩, hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hbox
    (ae_restrict_of_ae (ae_goodLagrangeParameters p g))
  exact ⟨b, v, fun t => ⟨(hb t (mem_univ t)).1, (hb t (mem_univ t)).2.le⟩, hgood⟩

/-- The fiber count `q^(a+m+|J|)` of a stratum, zero when `m + |J| > a`. -/
def stratumCount (q a m : ℕ) (J : Finset (Fin L)) : ℕ :=
  if m + J.card ≤ a then q ^ (a + m + J.card) else 0

/-- **L16 (one stratum).** -/
theorem volume_image_lagrangeSet_le (hD : 1 ≤ D) (p : PolyMap a m D)
    (g : Fin L → MvPolynomial (Fin a) ℝ) (hg : ∀ t, (g t).totalDegree ≤ D)
    {b : Fin L → ℝ} {v : Fin a → ℝ} (hgood : GoodLagrangeParameters p g b v)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hball : levelSource g b ⊆ closedBall 0 ρ) {B' : ℝ} (hB' : 0 ≤ B')
    (hJ : ∀ x ∈ levelSource g b, topRealJacobian (fderiv ℝ p.eval x) ≤ B')
    (J : Finset (Fin L)) :
    volume (p.eval '' lagrangeSet p g J b v) ≤
      ENNReal.ofReal ((4 : ℝ) ^ a) * (stratumCount (2 * D + 1) a m J : ℝ≥0∞) *
        euclideanUnitBallVolume m * ENNReal.ofReal (ρ ^ m) * ENNReal.ofReal B' := by
  by_cases hne : (lagrangeLevel p g J b v).Nonempty
  · have hmJ : m + J.card ≤ a := by
      obtain ⟨q, -, hq, -⟩ := hne
      simpa [Fintype.card_sum] using hq.fintype_card_le_finrank
    rw [stratumCount, ite_eq_left hmJ]
    obtain ⟨φ, Dm, hDm, hDcube, hφ, hinj, hder, hdis, hcover⟩ :=
      exists_lagrangeCharts p g J b v (hgood.2.1 J) hne
    have hsub := lagrangeSet_subset_levelSource p g J b v
    have hvol := volume_iUnion_C1Pieces_le φ Dm hDm hDcube hφ hinj hder hdis
      (lagrangeSet p g J b v) (fun n => hcover ▸ subset_iUnion (fun n => φ n '' Dm n) n)
      (hsub.trans hball) ((2 * D + 1) ^ (a + m + J.card))
      (fun I _ => by
        filter_upwards [hgood.2.2 J I] with z hz
        exact lagrangeSet_coordinateFiber_finite_card_le hD p g hg J I b v z hz)
      p.eval isOpen_univ (subset_univ _) p.contDiff_eval.contDiffOn hB'
      (fun x hx => hJ x (hsub hx))
    rw [hcover] at hvol
    exact hvol.trans_eq (coordinate_graph_volume_constant_eq a m _ hρ hB')
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hempty : lagrangeSet p g J b v = ∅ := by
      simp only [lagrangeSet, hne, Set.image_empty]
    rw [hempty, Set.image_empty, measure_empty]
    exact zero_le

/-- The strata with `|J| ≤ n` weighted by `q^|J|`: by
`Σ_J q^|J| c^(L-|J|) = (q+c)^L ≤ c^(L+2)` the sum is at most `c^(n+2)`. -/
theorem sum_stratumWeight_le {q c : ℕ} (hc : 1 ≤ c) (hqc : (q + c) ^ L ≤ c ^ (L + 2)) (n : ℕ) :
    ∑ J : Finset (Fin L), (if J.card ≤ n then q ^ J.card else 0) ≤ c ^ (n + 2) := by
  have key : ∀ J : Finset (Fin L), (if J.card ≤ n then q ^ J.card else 0) * c ^ L ≤
      c ^ n * (q ^ J.card * c ^ (L - J.card)) := by
    intro J
    split_ifs with h
    · have hJ : J.card ≤ L := by simpa using J.card_le_univ
      calc q ^ J.card * c ^ L
          = q ^ J.card * (c ^ J.card * c ^ (L - J.card)) := by
            rw [← pow_add, Nat.add_sub_cancel' hJ]
        _ ≤ q ^ J.card * (c ^ n * c ^ (L - J.card)) := by
            gcongr
        _ = c ^ n * (q ^ J.card * c ^ (L - J.card)) := by ring
    · simp
  have hsum : (∑ J : Finset (Fin L), (if J.card ≤ n then q ^ J.card else 0)) * c ^ L ≤
      c ^ n * (q + c) ^ L := by
    have hbin := Fintype.sum_pow_mul_eq_add_pow (Fin L) q c
    rw [Fintype.card_fin] at hbin
    calc _ = ∑ J : Finset (Fin L), (if J.card ≤ n then q ^ J.card else 0) * c ^ L :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ J : Finset (Fin L), c ^ n * (q ^ J.card * c ^ (L - J.card)) :=
          Finset.sum_le_sum fun J _ => key J
      _ = c ^ n * (q + c) ^ L := by rw [← Finset.mul_sum, hbin]
  refine Nat.le_of_mul_le_mul_right ?_ (pow_pos (by omega : 0 < c) L)
  calc _ ≤ c ^ n * (q + c) ^ L := hsum
    _ ≤ c ^ n * c ^ (L + 2) := Nat.mul_le_mul_left _ hqc
    _ = c ^ (n + 2) * c ^ L := by ring

/-- The stratum counts are at most `(q c)^(a+m)`. -/
theorem sum_stratumCount_le {q c : ℕ} (hc : 1 ≤ c) (hqc : (q + c) ^ L ≤ c ^ (L + 2))
    (hm : 1 ≤ m) :
    ∑ J : Finset (Fin L), stratumCount q a m J ≤ (q * c) ^ (a + m) := by
  by_cases ham : m ≤ a
  · obtain ⟨n, rfl⟩ : ∃ n, a = m + n := ⟨a - m, by omega⟩
    have hcount : ∀ J : Finset (Fin L), stratumCount q (m + n) m J =
        q ^ (m + n + m) * (if J.card ≤ n then q ^ J.card else 0) := by
      intro J
      unfold stratumCount
      by_cases h : J.card ≤ n
      · rw [ite_eq_left (by omega), ite_eq_left h, pow_add]
      · rw [ite_eq_right (by omega), ite_eq_right h, mul_zero]
    simp_rw [hcount, ← Finset.mul_sum]
    calc _ ≤ q ^ (m + n + m) * c ^ (n + 2) := by
          gcongr; exact sum_stratumWeight_le hc hqc n
      _ ≤ q ^ (m + n + m) * c ^ (m + n + m) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hc (by omega))
      _ = (q * c) ^ (m + n + m) := by rw [mul_pow]
  · have h0 : ∀ J : Finset (Fin L), stratumCount q a m J = 0 := fun J => by
      unfold stratumCount; rw [ite_eq_right (by omega)]
    simp [h0]

/-- The bound for a fixed `η > 0`. -/
theorem volume_image_le_add {c Δ : ℕ} (hΔ : 2 ≤ Δ) (F : PolyFormat a c Δ) (p : PolyMap a m Δ)
    (hm : 1 ≤ m) {R : ℝ} (hR : 0 ≤ R) (h3 : F.source ⊆ closedBall 0 R)
    {c' : ℕ} (hc' : 1 ≤ c') (hqc : (2 * Δ + 1 + c') ^ (2 * c + 1) ≤ c' ^ (2 * c + 1 + 2))
    {B : ℝ} (hB : 0 ≤ B)
    (hJ : ∀ x ∈ F.source, topRealJacobian (fderiv ℝ p.eval x) ≤ B) {η : ℝ} (hη : 0 < η) :
    volume (p.eval '' F.source) ≤
      ENNReal.ofReal ((max 4 (R + 1) * ((2 * Δ + 1) * c' : ℕ)) ^ (a + m)) *
        euclideanUnitBallVolume m * ENNReal.ofReal (B + η) := by
  classical
  have hD1 : 1 ≤ Δ := by omega
  set g := levelPolys F R with hg
  set U : Set (RealEuclidean a) := {x | topRealJacobian (fderiv ℝ p.eval x) < B + η} with hU
  have hUo : IsOpen U :=
    isOpen_lt (ContDiff.continuous_topRealJacobian_fderiv p.contDiff_eval) continuous_const
  have hSU : F.source ⊆ U := fun x hx => lt_of_le_of_lt (hJ x hx) (by linarith)
  obtain ⟨δ, hδ, -, hfam⟩ := exists_levelFamily F hR h3 hUo hSU
  obtain ⟨b, v, hb, hgood⟩ := exists_goodLagrangeParameters p g hδ
  obtain ⟨hSSb, hball, hcpt, hSbU⟩ := hfam b hb
  have hJb : ∀ x ∈ levelSource g b, topRealJacobian (fderiv ℝ p.eval x) ≤ B + η :=
    fun x hx => (hSbU hx).le
  set N : ℕ := ∑ J : Finset (Fin (2 * c + 1)), stratumCount (2 * Δ + 1) a m J with hN
  have hρ : (0 : ℝ) ≤ R + 1 := by linarith
  have hstrata : volume (⋃ J : Finset (Fin (2 * c + 1)), p.eval '' lagrangeSet p g J b v) ≤
      ENNReal.ofReal ((4 : ℝ) ^ a * N * (R + 1) ^ m) *
        euclideanUnitBallVolume m * ENNReal.ofReal (B + η) := by
    calc _ ≤ ∑' J : Finset (Fin (2 * c + 1)), volume (p.eval '' lagrangeSet p g J b v) :=
          measure_iUnion_le _
      _ ≤ ∑' J : Finset (Fin (2 * c + 1)), ENNReal.ofReal ((4 : ℝ) ^ a) *
            (stratumCount (2 * Δ + 1) a m J : ℝ≥0∞) * euclideanUnitBallVolume m *
            ENNReal.ofReal ((R + 1) ^ m) * ENNReal.ofReal (B + η) :=
          ENNReal.tsum_le_tsum fun J =>
            volume_image_lagrangeSet_le hD1 p g (levelPolys_degree_le hΔ F R) hgood hρ hball
              (by linarith) hJb J
      _ = _ := by
          rw [tsum_fintype, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast, hN, Nat.cast_sum, Finset.mul_sum, Finset.sum_mul,
            Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun J _ => ?_
          ring
  have hsing : volume (⋃ J : Finset (Fin (2 * c + 1)), singularLevelValues p g J b) = 0 :=
    measure_iUnion_null hgood.1
  have hreal : (4 : ℝ) ^ a * N * (R + 1) ^ m ≤
      (max 4 (R + 1) * ((2 * Δ + 1) * c' : ℕ)) ^ (a + m) := by
    have hNle : (N : ℝ) ≤ (((2 * Δ + 1) * c' : ℕ) : ℝ) ^ (a + m) := by
      exact_mod_cast sum_stratumCount_le hc' hqc hm
    have h4 : (4 : ℝ) ^ a ≤ max 4 (R + 1) ^ a := pow_le_pow_left₀ (by norm_num) (le_max_left _ _) _
    have hR1 : (R + 1) ^ m ≤ max 4 (R + 1) ^ m := pow_le_pow_left₀ hρ (le_max_right _ _) _
    calc (4 : ℝ) ^ a * N * (R + 1) ^ m
        ≤ max 4 (R + 1) ^ a * (((2 * Δ + 1) * c' : ℕ) : ℝ) ^ (a + m) * max 4 (R + 1) ^ m := by
          gcongr
      _ = _ := by rw [mul_pow, pow_add]; ring
  calc volume (p.eval '' F.source)
      ≤ volume (p.eval '' levelSource g b) := measure_mono (image_mono hSSb)
    _ ≤ volume ((⋃ J : Finset (Fin (2 * c + 1)), singularLevelValues p g J b) ∪
          ⋃ J : Finset (Fin (2 * c + 1)), p.eval '' lagrangeSet p g J b v) :=
        measure_mono (image_levelSource_subset p g b hcpt v)
    _ ≤ volume (⋃ J : Finset (Fin (2 * c + 1)), singularLevelValues p g J b) +
          volume (⋃ J : Finset (Fin (2 * c + 1)), p.eval '' lagrangeSet p g J b v) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal ((4 : ℝ) ^ a * N * (R + 1) ^ m) *
          euclideanUnitBallVolume m * ENNReal.ofReal (B + η) := by
        rw [hsing, zero_add]; exact hstrata
    _ ≤ _ := by gcongr

theorem euclideanUnitBallVolume_ne_top' (m : ℕ) : euclideanUnitBallVolume m ≠ ∞ :=
  measure_ball_lt_top.ne

/-- **The polynomial image-volume bound for general formats.** For a format with at most `c`
constraints of degree at most `Δ ≥ 2` on a source in the radius-`R` ball, a polynomial map
of degree at most `Δ` and any `c' ≥ 1` with `(2Δ+1+c')^(2c+1) ≤ c'^(2c+3)`,
`Vol_m(p(S)) ≤ (max(4, R+1)(2Δ+1)c')^(a+m) ω_m sup J_m p`. -/
theorem volume_image_le_of_polyFormat {c Δ : ℕ} (hΔ : 2 ≤ Δ) (F : PolyFormat a c Δ)
    (p : PolyMap a m Δ) (hm : 1 ≤ m) {R : ℝ} (hR : 0 ≤ R) (h3 : F.source ⊆ closedBall 0 R)
    {c' : ℕ} (hc' : 1 ≤ c') (hqc : (2 * Δ + 1 + c') ^ (2 * c + 1) ≤ c' ^ (2 * c + 1 + 2))
    {B : ℝ} (hB : 0 ≤ B) (hJ : ∀ x ∈ F.source, topRealJacobian (fderiv ℝ p.eval x) ≤ B) :
    volume (p.eval '' F.source) ≤
      ENNReal.ofReal ((max 4 (R + 1) * ((2 * Δ + 1) * c' : ℕ)) ^ (a + m)) *
        euclideanUnitBallVolume m * ENNReal.ofReal B := by
  have hK : ENNReal.ofReal ((max 4 (R + 1) * ((2 * Δ + 1) * c' : ℕ)) ^ (a + m)) *
      euclideanUnitBallVolume m ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (euclideanUnitBallVolume_ne_top' m)
  have hlim : Tendsto (fun j : ℕ => ENNReal.ofReal (B + 1 / ((j : ℝ) + 1))) atTop
      (𝓝 (ENNReal.ofReal B)) := by
    have hT : Tendsto (fun j : ℕ => B + 1 / ((j : ℝ) + 1)) atTop (𝓝 B) := by
      simpa only [add_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add B
    simpa only [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto B).comp hT
  exact ge_of_tendsto' (ENNReal.Tendsto.const_mul hlim (Or.inr hK))
    (fun j => volume_image_le_add hΔ F p hm hR h3 hc' hqc hB hJ (by positivity))

/-- The admissible count base `c' = (2Δ+2)·2^(2c+1)`. -/
theorem pow_add_le_of_polyFormat (c Δ : ℕ) :
    (2 * Δ + 1 + (2 * Δ + 2) * 2 ^ (2 * c + 1)) ^ (2 * c + 1) ≤
      ((2 * Δ + 2) * 2 ^ (2 * c + 1)) ^ (2 * c + 1 + 2) := by
  set L := 2 * c + 1
  set c' := (2 * Δ + 2) * 2 ^ L with hc'
  have h2L : 2 ^ L ≤ c' := by
    rw [hc']; exact Nat.le_mul_of_pos_left _ (by omega)
  have hq : 2 * Δ + 1 ≤ c' := by
    rw [hc']; nlinarith [Nat.one_le_two_pow (n := L)]
  calc (2 * Δ + 1 + c') ^ L ≤ (2 * c') ^ L := Nat.pow_le_pow_left (by omega) _
    _ = 2 ^ L * c' ^ L := by rw [mul_pow]
    _ ≤ (c' * c') * c' ^ L := Nat.mul_le_mul_right _ (h2L.trans (Nat.le_mul_self c'))
    _ = c' ^ (L + 2) := by ring

/-- **`lem:image-volume`.** For every degree budget `Δ₀ ≥ 2` and radius `R₀ ≥ 0` there is
`C ≥ 1` such that for all `k, m ≥ 1`, every basic closed source `Y ⊆ ℝ^k` with at most `Δ₀`
equations and weak inequalities of degree at most `Δ₀` inside the radius-`R₀` ball and every
polynomial map `φ : ℝ^k → ℝ^m` of degree at most `Δ₀`,
`Vol_m(φ(Y)) ≤ C^(k+m) ω_m sup_Y J_m φ`. -/
theorem exists_polynomialImageVolume_constant (Δ₀ : ℕ) (hΔ : 2 ≤ Δ₀) {R₀ : ℝ} (hR : 0 ≤ R₀) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (k m : ℕ), 1 ≤ k → 1 ≤ m →
      ∀ (F : PolyFormat k Δ₀ Δ₀) (φ : PolyMap k m Δ₀), F.source ⊆ closedBall 0 R₀ →
        ∀ B : ℝ, 0 ≤ B → (∀ x ∈ F.source, topRealJacobian (fderiv ℝ φ.eval x) ≤ B) →
          volume (φ.eval '' F.source) ≤
            ENNReal.ofReal (C ^ (k + m)) * euclideanUnitBallVolume m * ENNReal.ofReal B := by
  set c' := (2 * Δ₀ + 2) * 2 ^ (2 * Δ₀ + 1)
  have hc' : 1 ≤ c' := Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine ⟨max 4 (R₀ + 1) * ((2 * Δ₀ + 1) * c' : ℕ), ?_, fun k m _ hm F φ h3 B hB hJ =>
    volume_image_le_of_polyFormat hΔ F φ hm hR h3 hc' (pow_add_le_of_polyFormat Δ₀ Δ₀) hB hJ⟩
  have h1 : (1 : ℝ) ≤ ((2 * Δ₀ + 1) * c' : ℕ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  nlinarith [le_max_left (4 : ℝ) (R₀ + 1)]

/-- **The polynomial image-volume bound with the explicit constant `804 · 560`.** -/
theorem polynomialImageVolumeBoundWith : PolynomialImageVolumeBoundWith (804 * 560) := by
  intro a m _ha hm F p _hF h3 B hB hJ
  have h := volume_image_le_of_polyFormat (by norm_num : 2 ≤ 100) F.toPolyFormat p.toPolyMap hm
    (by norm_num : (0 : ℝ) ≤ 3) h3 (by norm_num : 1 ≤ 560) (by decide) hB hJ
  have hc : max 4 ((3 : ℝ) + 1) * (((2 * 100 + 1) * 560 : ℕ) : ℝ) = 804 * 560 := by norm_num
  rw [hc] at h
  simpa using h

/-- **`PolynomialImageVolumeBound` without external hypotheses.** -/
theorem polynomialImageVolumeBound : PolynomialImageVolumeBound :=
  ⟨804 * 560, by norm_num, polynomialImageVolumeBoundWith⟩

end NLQCLean.DirectVolume

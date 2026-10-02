import NLQCLean.Geometry.DirectVolume.Regularity
import NLQCLean.Semialgebraic.FinitePointCount

/-!
# Direct image-volume route: counting fiber points

Over a regular value `((b, v), z)` of the equal-dimensional map `K`, the fiber
`K⁻¹((b, v), z)` is the zero set of one nonnegative polynomial `Φ` of degree at
most 200, and each of its points is isolated. On this fiber the inactive
multipliers `μ_t`, `t ∉ J`, are frozen at the levels `b_t`, so substituting them
leaves a polynomial in the `a + m + |J|` free coordinates with isolated zeros.
The point count for isolated zeros (P5) bounds it by `201^(a+m+|J|)`, and every
point of a coordinate fiber of a Lagrange set lifts into it (L12–L15). Roadmap
step D6 (`D0-PROOF.md` §10).
-/

namespace NLQCLean.DirectVolume

open MvPolynomial Set Function Filter Topology

variable {a m : ℕ}

/-- `pderiv` lowers the total degree by one (repair R2 of the D0 review). -/
theorem totalDegree_pderiv_le_pred {σ : Type*} [DecidableEq σ] (P : MvPolynomial σ ℝ)
    (k : σ) : (pderiv k P).totalDegree ≤ P.totalDegree - 1 := by
  by_cases h : pderiv k P = 0
  · rw [h, totalDegree_zero]; exact Nat.zero_le _
  · have := totalDegree_pderiv_lt h
    omega

theorem totalDegree_X_mul_pderiv_le {N : ℕ} (P : MvPolynomial (Fin a) ℝ)
    (hP : P.totalDegree ≤ 100) (r : Fin N) (f : Fin a → Fin N) (k : Fin a) :
    (X r * rename f (pderiv k P)).totalDegree ≤ 100 := by
  refine (totalDegree_mul _ _).trans ?_
  have h1 : (X r : MvPolynomial (Fin N) ℝ).totalDegree ≤ 1 := by rw [totalDegree_X]
  have h2 := (totalDegree_rename_le f (pderiv k P)).trans (totalDegree_pderiv_le_pred P k)
  omega

/-- The lifted nonnegative polynomial `Φ`. -/
noncomputable def lagrangePhi (p : BoundedPolynomialMap a m)
    (g : Fin 41 → MvPolynomial (Fin a) ℝ) (J : Finset (Fin 41)) (I : Fin m → Fin a)
    (b : Fin 41 → ℝ) (v : Fin a → ℝ) (z : RealEuclidean m) :
    MvPolynomial (Fin (a + m + 41)) ℝ :=
  ∑ t, (lagrangeValuePoly g J t - C (b t)) ^ 2 +
    ∑ k, (lagrangeGradPoly p g J k - C (v k)) ^ 2 +
    ∑ j, (X (ixL a m (I j)) - C (z j)) ^ 2

theorem eval_lagrangePhi_nonneg (p : BoundedPolynomialMap a m)
    (g : Fin 41 → MvPolynomial (Fin a) ℝ) (J : Finset (Fin 41)) (I : Fin m → Fin a)
    (b : Fin 41 → ℝ) (v : Fin a → ℝ) (z : RealEuclidean m) (q : Fin (a + m + 41) → ℝ) :
    0 ≤ eval q (lagrangePhi p g J I b v z) := by
  simp only [lagrangePhi, map_add, map_sum, map_pow]
  positivity

/-- **L12 (b).** The zero set of `Φ` is the fiber of `K`. -/
theorem eval_lagrangePhi_eq_zero_iff (p : BoundedPolynomialMap a m)
    (g : Fin 41 → MvPolynomial (Fin a) ℝ) (J : Finset (Fin 41)) (I : Fin m → Fin a)
    (b : Fin 41 → ℝ) (v : Fin a → ℝ) (z : RealEuclidean m) (q : Fin (a + m + 41) → ℝ) :
    eval q (lagrangePhi p g J I b v z) = 0 ↔ lagrangeCoordMap p g J I q = ((b, v), z) := by
  simp only [lagrangePhi, map_add, map_sum, map_pow, map_sub, eval_C, eval_X]
  have h1 : 0 ≤ ∑ t, (eval q (lagrangeValuePoly g J t) - b t) ^ 2 := by positivity
  have h2 : 0 ≤ ∑ k, (eval q (lagrangeGradPoly p g J k) - v k) ^ 2 := by positivity
  have h3 : 0 ≤ ∑ j, (q (ixL a m (I j)) - z j) ^ 2 := by positivity
  rw [add_eq_zero_iff_of_nonneg (add_nonneg h1 h2) h3, add_eq_zero_iff_of_nonneg h1 h2,
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _),
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _),
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  simp only [Finset.mem_univ, true_implies, pow_eq_zero_iff two_ne_zero, sub_eq_zero]
  simp only [lagrangeCoordMap, lagrangeMap, Prod.mk.injEq, funext_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    ext j
    simp [coordinateProjection, liftX, h3 j]
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, h2⟩, fun j => ?_⟩
    have := congrArg (fun w : RealEuclidean m => w j) h3
    simpa [coordinateProjection, liftX] using this

/-- **L12 (c).** `Φ` has total degree at most `2 · 100`. -/
theorem totalDegree_lagrangePhi_le (p : BoundedPolynomialMap a m)
    (g : Fin 41 → MvPolynomial (Fin a) ℝ) (hg : ∀ t, (g t).totalDegree ≤ 100)
    (J : Finset (Fin 41)) (I : Fin m → Fin a) (b : Fin 41 → ℝ) (v : Fin a → ℝ)
    (z : RealEuclidean m) : (lagrangePhi p g J I b v z).totalDegree ≤ 2 * 100 := by
  have hsq : ∀ P : MvPolynomial (Fin (a + m + 41)) ℝ, P.totalDegree ≤ 100 →
      ∀ c : ℝ, ((P - C c) ^ 2).totalDegree ≤ 2 * 100 := fun P hP c =>
    (totalDegree_pow _ 2).trans (Nat.mul_le_mul_left 2
      ((totalDegree_sub _ _).trans (max_le hP (by rw [totalDegree_C]; omega))))
  have hval : ∀ t, (lagrangeValuePoly (m := m) g J t).totalDegree ≤ 100 := by
    intro t
    unfold lagrangeValuePoly
    split_ifs
    · exact (totalDegree_rename_le _ _).trans (hg t)
    · rw [totalDegree_X]; omega
  have hgrad : ∀ k, (lagrangeGradPoly p g J k).totalDegree ≤ 100 := by
    intro k
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact totalDegree_finsetSum_le fun i _ =>
        totalDegree_X_mul_pderiv_le _ (p.degree_le i) _ _ k
    · exact totalDegree_finsetSum_le fun t _ =>
        totalDegree_X_mul_pderiv_le _ (hg t) _ _ k
  refine (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le ?_ ?_)) ?_)
  · exact totalDegree_finsetSum_le fun t _ => hsq _ (hval t) _
  · exact totalDegree_finsetSum_le fun k _ => hsq _ (hgrad k) _
  · exact totalDegree_finsetSum_le fun j _ => hsq _ (by rw [totalDegree_X]; omega) _

theorem finrank_lagrangeCoordMap_target :
    Module.finrank ℝ (((Fin 41 → ℝ) × (Fin a → ℝ)) × RealEuclidean m) = a + m + 41 := by
  simp only [Module.finrank_prod, Module.finrank_fin_fun, finrank_euclideanSpace_fin]
  ring

/-- **L13.** A regular point of an equal-dimensional smooth map is isolated in
its fiber. -/
theorem eventually_ne_of_surjective_fderiv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (hdim : Module.finrank ℝ E = Module.finrank ℝ F) {f : E → F}
    {q : E} (hf : DifferentiableAt ℝ f q) (hs : Surjective (fderiv ℝ f q)) :
    ∀ᶠ q' in 𝓝[≠] q, f q' ≠ f q := by
  have hinj : Injective (fderiv ℝ f q) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (fderiv ℝ f q : E →ₗ[ℝ] F))).mpr hs
  obtain ⟨C, -, hC⟩ := (LinearMap.injective_iff_antilipschitz
    (fderiv ℝ f q : E →ₗ[ℝ] F)).mp hinj
  exact hf.hasFDerivAt.eventually_ne ⟨C, hC⟩

/-- **L14.** A zero set of isolated zeros of a nonnegative polynomial is finite,
with the point bound of P5. -/
theorem zeroSet_finite_ncard_le_of_isolated {N D : ℕ} {F : MvPolynomial (Fin N) ℝ}
    (hF : F.totalDegree ≤ 2 * D) (hnn : ∀ x, 0 ≤ eval x F)
    (hiso : ∀ p, eval p F = 0 → ∀ᶠ x in 𝓝[≠] p, eval x F ≠ 0) :
    {x | eval x F = 0}.Finite ∧ {x | eval x F = 0}.ncard ≤ (2 * D + 1) ^ N := by
  have hcard : ∀ T : Finset (Fin N → ℝ), ↑T ⊆ {x | eval x F = 0} → T.card ≤ (2 * D + 1) ^ N :=
    fun T hT => PurePowerZeros.card_isolatedZeros_le hF hnn T fun p hp => ⟨hT hp, hiso p (hT hp)⟩
  have hfin : {x | eval x F = 0}.Finite := by
    by_contra hinf
    obtain ⟨T, hT, hTc⟩ := Set.Infinite.exists_subset_card_eq hinf ((2 * D + 1) ^ N + 1)
    have := hcard T hT
    omega
  refine ⟨hfin, ?_⟩
  obtain ⟨T, hT⟩ := hfin.exists_finset_coe
  rw [← hT, Set.ncard_coe_finset]
  exact hcard T hT.le

/-- A substitution of polynomials of degree at most one does not raise the total degree. -/
theorem totalDegree_bind₁_le {σ τ : Type*} (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ i, (f i).totalDegree ≤ 1) (φ : MvPolynomial σ ℝ) :
    (bind₁ f φ).totalDegree ≤ φ.totalDegree := by
  conv_lhs => rw [φ.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ((Finset.sum_le_sum fun i _ =>
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hf i))).trans ?_)
  simpa [Finsupp.sum] using le_totalDegree hs

/-- The lifted point whose inactive multipliers are frozen at their levels; the free
coordinates are `x`, `λ` and the active multipliers `μ_J`. -/
noncomputable def freezePoint (J : Finset (Fin 41)) (b : Fin 41 → ℝ)
    (w : Fin (a + m + J.card) → ℝ) : Fin (a + m + 41) → ℝ :=
  Fin.append (fun i => w (Fin.castAdd J.card i))
    (fun t => if h : t ∈ J then w (Fin.natAdd (a + m) (J.equivFin ⟨t, h⟩)) else b t)

/-- The free coordinates of a lifted point. -/
noncomputable def freeCoords (J : Finset (Fin 41)) (q : Fin (a + m + 41) → ℝ) :
    Fin (a + m + J.card) → ℝ :=
  Fin.append (fun i => q (Fin.castAdd 41 i))
    (fun j => q (Fin.natAdd (a + m) (J.equivFin.symm j : Fin 41)))

/-- The polynomial substitution realizing `freezePoint`. -/
noncomputable def freezeSubst (J : Finset (Fin 41)) (b : Fin 41 → ℝ) :
    Fin (a + m + 41) → MvPolynomial (Fin (a + m + J.card)) ℝ :=
  Fin.append (fun i => X (Fin.castAdd J.card i))
    (fun t => if h : t ∈ J then X (Fin.natAdd (a + m) (J.equivFin ⟨t, h⟩)) else C (b t))

theorem eval_freezeSubst (J : Finset (Fin 41)) (b : Fin 41 → ℝ)
    (w : Fin (a + m + J.card) → ℝ) (i : Fin (a + m + 41)) :
    eval w (freezeSubst J b i) = freezePoint J b w i := by
  refine Fin.addCases (fun i => ?_) (fun t => ?_) i
  · simp [freezeSubst, freezePoint]
  · by_cases h : t ∈ J <;> simp [freezeSubst, freezePoint, h]

theorem eval_bind₁_freezeSubst (J : Finset (Fin 41)) (b : Fin 41 → ℝ)
    (φ : MvPolynomial (Fin (a + m + 41)) ℝ) (w : Fin (a + m + J.card) → ℝ) :
    eval w (bind₁ (freezeSubst J b) φ) = eval (freezePoint J b w) φ := by
  have := eval₂Hom_bind₁ (RingHom.id ℝ) w (freezeSubst J b) φ
  simp only [coe_eval₂Hom] at this
  change eval₂ (RingHom.id ℝ) w _ = eval₂ (RingHom.id ℝ) _ φ at this
  rw [show (fun i => eval₂ (RingHom.id ℝ) w (freezeSubst J b i)) = freezePoint J b w from
    funext fun i => eval_freezeSubst J b w i] at this
  exact this

theorem totalDegree_freezeSubst_le (J : Finset (Fin 41)) (b : Fin 41 → ℝ)
    (i : Fin (a + m + 41)) : (freezeSubst (a := a) (m := m) J b i).totalDegree ≤ 1 := by
  refine Fin.addCases (fun i => ?_) (fun t => ?_) i
  · simp [freezeSubst]
  · by_cases h : t ∈ J <;> simp [freezeSubst, h]

theorem continuous_freezePoint (J : Finset (Fin 41)) (b : Fin 41 → ℝ) :
    Continuous (freezePoint (a := a) (m := m) J b) := by
  refine continuous_pi fun i => ?_
  simp_rw [← eval_freezeSubst J b _ i]
  exact MvPolynomial.continuous_eval _

theorem freeCoords_freezePoint (J : Finset (Fin 41)) (b : Fin 41 → ℝ)
    (w : Fin (a + m + J.card) → ℝ) : freeCoords J (freezePoint J b w) = w := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · simp [freeCoords, freezePoint]
  · simp [freeCoords, freezePoint]

theorem freezePoint_freeCoords (J : Finset (Fin 41)) (b : Fin 41 → ℝ)
    (q : Fin (a + m + 41) → ℝ) (hq : ∀ t ∉ J, q (imL a m t) = b t) :
    freezePoint J b (freeCoords J q) = q := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun t => ?_) i
  · simp [freeCoords, freezePoint]
  · by_cases h : t ∈ J
    · simp [freeCoords, freezePoint, h]
    · simpa [freezePoint, h, imL] using (hq t h).symm

/-- On the fiber of the Lagrange map over `(b, v)` the inactive multipliers equal
their levels. -/
theorem lagrangeMap_inactive (p : BoundedPolynomialMap a m)
    (g : Fin 41 → MvPolynomial (Fin a) ℝ) (J : Finset (Fin 41)) {b : Fin 41 → ℝ}
    {v : Fin a → ℝ} {q : Fin (a + m + 41) → ℝ} (hq : lagrangeMap p g J q = (b, v)) :
    ∀ t ∉ J, q (imL a m t) = b t := by
  intro t ht
  have := congrFun (congrArg Prod.fst hq) t
  simpa [lagrangeMap, lagrangeValuePoly, ht] using this

/-- **L15 (fiber count).** Over a slice value at which `K` is regular, a
coordinate fiber of a Lagrange set has at most `201^(a+m+|J|)` points. -/
theorem lagrangeSet_coordinateFiber_finite_card_le (p : BoundedPolynomialMap a m)
    (g : Fin 41 → MvPolynomial (Fin a) ℝ) (hg : ∀ t, (g t).totalDegree ≤ 100)
    (J : Finset (Fin 41)) (I : Fin m → Fin a) (b : Fin 41 → ℝ) (v : Fin a → ℝ)
    (z : RealEuclidean m)
    (hreg : ∀ q, lagrangeCoordMap p g J I q = ((b, v), z) →
      Surjective (fderiv ℝ (lagrangeCoordMap p g J I) q)) :
    (semialgebraicMapFiber (lagrangeSet p g J b v) (coordinateProjection I) z).Finite ∧
      Nat.card (semialgebraicMapFiber (lagrangeSet p g J b v) (coordinateProjection I) z) ≤
        201 ^ (a + m + J.card) := by
  set Φ := lagrangePhi p g J I b v z with hΦ
  set Ψ := bind₁ (freezeSubst J b) Φ with hΨ
  set E := freezePoint (a := a) (m := m) J b with hE
  have hEΨ : ∀ w, eval w Ψ = eval (E w) Φ := eval_bind₁_freezeSubst J b Φ
  have hEinj : Injective E := fun w w' h => by
    rw [← freeCoords_freezePoint J b w, ← freeCoords_freezePoint J b w']
    exact congrArg (freeCoords J) h
  have hiso : ∀ q, eval q Φ = 0 → ∀ᶠ q' in 𝓝[≠] q, eval q' Φ ≠ 0 := by
    intro q hq
    have hK := (eval_lagrangePhi_eq_zero_iff p g J I b v z q).mp hq
    have hdiff : DifferentiableAt ℝ (lagrangeCoordMap p g J I) q :=
      ((contDiff_lagrangeCoordMap p g J I).differentiable (by simp)).differentiableAt
    filter_upwards [eventually_ne_of_surjective_fderiv
      (by rw [finrank_lagrangeCoordMap_target, Module.finrank_fin_fun]) hdiff (hreg q hK)]
      with q' hq' h0
    exact hq' (((eval_lagrangePhi_eq_zero_iff p g J I b v z q').mp h0).trans hK.symm)
  have hisoΨ : ∀ w, eval w Ψ = 0 → ∀ᶠ w' in 𝓝[≠] w, eval w' Ψ ≠ 0 := by
    intro w hw
    have hT : Tendsto E (𝓝[≠] w) (𝓝[≠] (E w)) :=
      ((continuous_freezePoint J b).continuousWithinAt).tendsto_nhdsWithin
        fun w' hw' => hEinj.ne hw'
    filter_upwards [hT.eventually (hiso (E w) ((hEΨ w) ▸ hw))] with w' hw'
    rwa [hEΨ]
  have hdeg : Ψ.totalDegree ≤ 2 * 100 :=
    (totalDegree_bind₁_le _ (totalDegree_freezeSubst_le J b) Φ).trans
      (totalDegree_lagrangePhi_le p g hg J I b v z)
  obtain ⟨hZfin, hZcard⟩ := zeroSet_finite_ncard_le_of_isolated (D := 100) hdeg
    (fun w => (hEΨ w) ▸ eval_lagrangePhi_nonneg p g J I b v z (E w)) hisoΨ
  have hsub : semialgebraicMapFiber (lagrangeSet p g J b v) (coordinateProjection I) z ⊆
      (liftX ∘ E) '' {w | eval w Ψ = 0} := by
    rintro x ⟨⟨q, ⟨hq, -⟩, rfl⟩, hz⟩
    have hqE : E (freeCoords J q) = q :=
      freezePoint_freeCoords J b q (lagrangeMap_inactive p g J (Set.mem_singleton_iff.mp hq))
    refine ⟨freeCoords J q, ?_, by simp only [Function.comp_apply, hqE]⟩
    show eval _ Ψ = 0
    rw [hEΨ, hqE, eval_lagrangePhi_eq_zero_iff]
    simp only [lagrangeCoordMap, Prod.mk.injEq]
    exact ⟨Set.mem_singleton_iff.mp hq, hz⟩
  have himfin := hZfin.image (liftX ∘ E)
  refine ⟨himfin.subset hsub, ?_⟩
  rw [Nat.card_coe_set_eq]
  calc _ ≤ ((liftX ∘ E) '' {w | eval w Ψ = 0}).ncard := Set.ncard_le_ncard hsub himfin
    _ ≤ {w | eval w Ψ = 0}.ncard := Set.ncard_image_le hZfin
    _ ≤ (2 * 100 + 1) ^ (a + m + J.card) := hZcard

end NLQCLean.DirectVolume

import NLQCLean.Geometry.DirectVolume.Strata

/-!
# Direct image-volume route: the Lagrange-maximum covering

The lifted space `Fin (a+m+41) → ℝ` carries a point `x`, multipliers `λ` for the
components of `p` and multipliers `μ` for the 41 constraints. For a stratum `J`
the Lagrange map sends `(x, λ, μ)` to the active constraint values (masked by
`μ_t` off `J`) and to the multiplier combination of gradients. Its level set over
`(b, v)`, restricted to independent gradients and strict inactive constraints,
projects to the Lagrange set `L_J(b, v)`.

**Covering (L6).** Every value `y` of `p` on the level source `S_b` is either a
singular value of some stratum or the image of a point of some Lagrange set: the
maximizer of `⟨v, ·⟩` on the fiber over `y` is a Lagrange point.
Roadmap step D4 (`D0-PROOF.md` §7).
-/

namespace NLQCLean.DirectVolume

open MvPolynomial Set Function

variable {a m : ℕ}

/-- Coordinates of the point `x` in the lifted space. -/
def ixL (a m : ℕ) (k : Fin a) : Fin (a + m + 41) := Fin.castAdd 41 (Fin.castAdd m k)
/-- Coordinates of the multipliers of `p`. -/
def ilL (a m : ℕ) (i : Fin m) : Fin (a + m + 41) := Fin.castAdd 41 (Fin.natAdd a i)
/-- Coordinates of the multipliers of the constraints. -/
def imL (a m : ℕ) (t : Fin 41) : Fin (a + m + 41) := Fin.natAdd (a + m) t

/-- The point component of a lifted point. -/
noncomputable def liftX (q : Fin (a + m + 41) → ℝ) : RealEuclidean a :=
  WithLp.toLp 2 fun k => q (ixL a m k)

theorem continuous_liftX : Continuous (liftX : (Fin (a + m + 41) → ℝ) → RealEuclidean a) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin a => ℝ)).symm.continuous.comp
    (continuous_pi fun k => continuous_apply (ixL a m k))

theorem evalE_liftX (P : MvPolynomial (Fin a) ℝ) (q : Fin (a + m + 41) → ℝ) :
    evalE P (liftX q) = eval q (rename (ixL a m) P) := by
  simp [evalE, liftX, eval_rename, Function.comp_def]

/-- The lifted point with prescribed components. -/
def liftPoint (x : Fin a → ℝ) (l : Fin m → ℝ) (u : Fin 41 → ℝ) : Fin (a + m + 41) → ℝ :=
  Fin.append (Fin.append x l) u

@[simp] theorem liftPoint_ixL (x : Fin a → ℝ) (l : Fin m → ℝ) (u : Fin 41 → ℝ) (k : Fin a) :
    liftPoint x l u (ixL a m k) = x k := by
  simp [liftPoint, ixL]

@[simp] theorem liftPoint_ilL (x : Fin a → ℝ) (l : Fin m → ℝ) (u : Fin 41 → ℝ) (i : Fin m) :
    liftPoint x l u (ilL a m i) = l i := by
  simp [liftPoint, ilL]

@[simp] theorem liftPoint_imL (x : Fin a → ℝ) (l : Fin m → ℝ) (u : Fin 41 → ℝ) (t : Fin 41) :
    liftPoint x l u (imL a m t) = u t := by
  simp [liftPoint, imL]

/-- The constraint-value polynomials of a stratum, masked off `J`. -/
noncomputable def lagrangeValuePoly (g : Fin 41 → MvPolynomial (Fin a) ℝ) (J : Finset (Fin 41))
    (t : Fin 41) : MvPolynomial (Fin (a + m + 41)) ℝ :=
  if t ∈ J then rename (ixL a m) (g t) else X (imL a m t)

/-- The multiplier combination of gradients. -/
noncomputable def lagrangeGradPoly (p : BoundedPolynomialMap a m)
    (g : Fin 41 → MvPolynomial (Fin a) ℝ) (J : Finset (Fin 41)) (k : Fin a) :
    MvPolynomial (Fin (a + m + 41)) ℝ :=
  ∑ i, X (ilL a m i) * rename (ixL a m) (pderiv k (p.coordinates i)) +
    ∑ t ∈ J, X (imL a m t) * rename (ixL a m) (pderiv k (g t))

/-- The Lagrange map of a stratum. -/
noncomputable def lagrangeMap (p : BoundedPolynomialMap a m)
    (g : Fin 41 → MvPolynomial (Fin a) ℝ) (J : Finset (Fin 41)) (q : Fin (a + m + 41) → ℝ) :
    (Fin 41 → ℝ) × (Fin a → ℝ) :=
  (fun t => eval q (lagrangeValuePoly g J t), fun k => eval q (lagrangeGradPoly p g J k))

/-- Independent gradients and strict inactive constraints. -/
def lagrangeOpen (p : BoundedPolynomialMap a m) (g : Fin 41 → MvPolynomial (Fin a) ℝ)
    (J : Finset (Fin 41)) (b : Fin 41 → ℝ) : Set (Fin (a + m + 41) → ℝ) :=
  {q | LinearIndependent ℝ (lagrangeGradients p g J (liftX q)) ∧
    ∀ t ∉ J, b t < evalE (g t) (liftX q)}

/-- The lifted Lagrange level set. -/
def lagrangeLevel (p : BoundedPolynomialMap a m) (g : Fin 41 → MvPolynomial (Fin a) ℝ)
    (J : Finset (Fin 41)) (b : Fin 41 → ℝ) (v : Fin a → ℝ) : Set (Fin (a + m + 41) → ℝ) :=
  lagrangeMap p g J ⁻¹' {(b, v)} ∩ lagrangeOpen p g J b

/-- The Lagrange set `L_J(b, v)`. -/
def lagrangeSet (p : BoundedPolynomialMap a m) (g : Fin 41 → MvPolynomial (Fin a) ℝ)
    (J : Finset (Fin 41)) (b : Fin 41 → ℝ) (v : Fin a → ℝ) : Set (RealEuclidean a) :=
  liftX '' lagrangeLevel p g J b v

theorem continuous_lagrangeGradients_liftX (p : BoundedPolynomialMap a m)
    (g : Fin 41 → MvPolynomial (Fin a) ℝ) (J : Finset (Fin 41)) :
    Continuous fun q : Fin (a + m + 41) → ℝ => lagrangeGradients p g J (liftX q) := by
  refine continuous_pi fun σ => continuous_pi fun k => ?_
  rcases σ with i | t
  · exact (contDiff_evalE _).continuous.comp continuous_liftX
  · exact (contDiff_evalE _).continuous.comp continuous_liftX

/-- **L5.** The open part of the Lagrange system is open. -/
theorem isOpen_lagrangeOpen (p : BoundedPolynomialMap a m)
    (g : Fin 41 → MvPolynomial (Fin a) ℝ) (J : Finset (Fin 41)) (b : Fin 41 → ℝ) :
    IsOpen (lagrangeOpen p g J b) := by
  have h2 : IsOpen {q : Fin (a + m + 41) → ℝ | ∀ t ∉ J, b t < evalE (g t) (liftX q)} := by
    have : {q : Fin (a + m + 41) → ℝ | ∀ t ∉ J, b t < evalE (g t) (liftX q)} =
        ⋂ t ∈ (Finset.univ.filter fun t => t ∉ J), {q | b t < evalE (g t) (liftX q)} := by
      ext q; simp
    rw [this]
    exact isOpen_biInter_finset fun t _ =>
      isOpen_lt continuous_const ((contDiff_evalE _).continuous.comp continuous_liftX)
  exact (isOpen_setOfPred_linearIndependent.preimage
    (continuous_lagrangeGradients_liftX p g J)).inter h2

theorem lagrangeSet_subset_levelSource (p : BoundedPolynomialMap a m)
    (g : Fin 41 → MvPolynomial (Fin a) ℝ) (J : Finset (Fin 41)) (b : Fin 41 → ℝ)
    (v : Fin a → ℝ) : lagrangeSet p g J b v ⊆ levelSource g b := by
  rintro _ ⟨q, ⟨hq, hopen⟩, rfl⟩ t
  by_cases ht : t ∈ J
  · have := congrFun (congrArg Prod.fst (Set.mem_singleton_iff.mp hq)) t
    simp only [lagrangeMap, lagrangeValuePoly, ht, ite_true] at this
    rw [evalE_liftX, this]
  · exact (hopen.2 t ht).le

/-- The linear functional `x ↦ Σ_k w_k x_k` of a coefficient vector. -/
noncomputable def dualOf (a : ℕ) : (Fin a → ℝ) →ₗ[ℝ] StrongDual ℝ (RealEuclidean a) where
  toFun w := ∑ k, w k • (EuclideanSpace.proj k : RealEuclidean a →L[ℝ] ℝ)
  map_add' w w' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c w := by simp [Finset.smul_sum, smul_smul]

theorem dualOf_apply (w : Fin a → ℝ) (x : RealEuclidean a) :
    dualOf a w x = ∑ k, w k * x k := by
  simp [dualOf]

theorem dualOf_injective : Function.Injective (dualOf a) := by
  intro w w' h
  funext k
  have := congrArg (fun L : StrongDual ℝ (RealEuclidean a) => L (EuclideanSpace.single k 1)) h
  simpa [dualOf_apply, PiLp.single_apply] using this

theorem gradE_eq_dualOf (P : MvPolynomial (Fin a) ℝ) (x : RealEuclidean a) :
    gradE P x = dualOf a (fun k => evalE (pderiv k P) x) := by
  ext v
  rw [gradE_apply, dualOf_apply]

/-- **L6 (Lagrange-maximum covering).** -/
theorem image_levelSource_subset (p : BoundedPolynomialMap a m)
    (g : Fin 41 → MvPolynomial (Fin a) ℝ) (b : Fin 41 → ℝ)
    (hK : IsCompact (levelSource g b)) (v : Fin a → ℝ) :
    p.eval '' levelSource g b ⊆
      (⋃ J : Finset (Fin 41), singularLevelValues p g J b) ∪
        ⋃ J : Finset (Fin 41), p.eval '' lagrangeSet p g J b v := by
  classical
  rintro y ⟨x₀, hx₀, rfl⟩
  set y := p.eval x₀ with hy
  -- The compact fiber and the maximizer of `⟨v, ·⟩` on it.
  set Fy := levelSource g b ∩ p.eval ⁻¹' {y} with hFy
  have hFyc : IsCompact Fy :=
    hK.inter_right ((isClosed_singleton.preimage p.contDiff_eval.continuous))
  set φL : RealEuclidean a →L[ℝ] ℝ := dualOf a v with hφL
  obtain ⟨xs, hxs, hmax⟩ := hFyc.exists_isMaxOn ⟨x₀, hx₀, rfl⟩ φL.continuous.continuousOn
  have hxsS : xs ∈ levelSource g b := hxs.1
  have hxsy : p.eval xs = y := hxs.2
  set J : Finset (Fin 41) := Finset.univ.filter fun t => evalE (g t) xs = b t with hJ
  by_cases hsing : y ∈ singularLevelValues p g J b
  · exact Or.inl (mem_iUnion.mpr ⟨J, hsing⟩)
  refine Or.inr (mem_iUnion.mpr ⟨J, ?_⟩)
  have hJact : ∀ t ∈ J, evalE (g t) xs = b t := fun t ht => (Finset.mem_filter.mp ht).2
  have hsurj : Surjective (fderiv ℝ (maskedLevelMap p g J) (xs, b)) := by
    by_contra h
    exact hsing ⟨xs, hJact, hxsy, h⟩
  have hind := linearIndependent_of_surjective_masked p g J hsurj
  -- Constraint functions and their strict derivatives.
  let f : Fin m ⊕ J → RealEuclidean a → ℝ
    | .inl i => evalE (p.coordinates i)
    | .inr t => evalE (g t)
  let f' : Fin m ⊕ J → StrongDual ℝ (RealEuclidean a)
    | .inl i => gradE (p.coordinates i) xs
    | .inr t => gradE (g t) xs
  have hf' : ∀ σ, HasStrictFDerivAt (f σ) (f' σ) xs := by
    rintro (i | t) <;> exact hasStrictFDerivAt_evalE _ xs
  have hf'eq : f' = fun σ => dualOf a (lagrangeGradients p g J xs σ) := by
    funext σ
    rcases σ with i | t <;> exact gradE_eq_dualOf _ xs
  have hind' : LinearIndependent ℝ f' := by
    rw [hf'eq]
    exact hind.map' (dualOf a) (LinearMap.ker_eq_bot.mpr dualOf_injective)
  -- `xs` is a local maximum on the equality stratum.
  set V : Set (RealEuclidean a) := {x | ∀ t ∉ J, b t < evalE (g t) x} with hV
  have hVo : IsOpen V := by
    have : V = ⋂ t ∈ (Finset.univ.filter fun t => t ∉ J), {x | b t < evalE (g t) x} := by
      ext x; simp [hV]
    rw [this]
    exact isOpen_biInter_finset fun t _ => isOpen_lt continuous_const (contDiff_evalE _).continuous
  have hxsV : xs ∈ V := by
    intro t ht
    refine lt_of_le_of_ne (hxsS t) fun h => ht ?_
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.symm⟩
  have hextr : IsLocalExtrOn φL {x | ∀ σ, f σ x = f σ xs} xs := by
    refine Or.inr ?_
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hVo.mem_nhds hxsV)]
      with x hx hxV
    apply hmax
    refine ⟨fun t => ?_, ?_⟩
    · by_cases ht : t ∈ J
      · have := hx (.inr ⟨t, ht⟩)
        simp only [f] at this
        rw [this, hJact t ht]
      · exact (hxV t ht).le
    · show p.eval x = y
      rw [← hxsy]
      ext i
      have := hx (.inl i)
      simpa [f, BoundedPolynomialMap.eval, evalE] using this
  -- Lagrange multipliers.
  obtain ⟨μ, hμ⟩ := PolynomialCalculus.IsLocalExtrOn.exists_lagrange_of_linearIndependent
    hextr hf' φL.hasStrictFDerivAt hind'
  have hcomb : ∀ k, v k = ∑ i, μ (.inl i) * evalE (pderiv k (p.coordinates i)) xs +
      ∑ t : J, μ (.inr t) * evalE (pderiv k (g t)) xs := by
    intro k
    have := congrArg (fun L : StrongDual ℝ (RealEuclidean a) => L (EuclideanSpace.single k 1)) hμ
    simp only [hφL, dualOf_apply, PiLp.single_apply] at this
    rw [Fintype.sum_sum_type] at this
    simpa [f', gradE_apply, PiLp.single_apply, mul_comm] using this
  -- The lifted point.
  set u : Fin 41 → ℝ := fun t => if ht : t ∈ J then μ (.inr ⟨t, ht⟩) else b t with hu
  set q := liftPoint (fun k => xs k) (fun i => μ (.inl i)) u with hq
  have hliftq : liftX q = xs := by
    ext k; simp [liftX, hq]
  refine ⟨xs, ⟨q, ⟨?_, ?_⟩, hliftq⟩, hxsy⟩
  · rw [Set.mem_preimage, Set.mem_singleton_iff, lagrangeMap, Prod.mk.injEq]
    constructor
    · funext t
      by_cases ht : t ∈ J
      · simp only [lagrangeValuePoly, ht, ite_true]
        rw [← evalE_liftX, hliftq, hJact t ht]
      · simp [lagrangeValuePoly, ht, hq, hu]
    · funext k
      rw [hcomb k]
      simp only [lagrangeGradPoly, map_add, map_sum, map_mul, eval_X, hq, liftPoint_ilL,
        liftPoint_imL]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [← evalE_liftX, ← hq, hliftq]
      · rw [← Finset.sum_coe_sort J]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← evalE_liftX, ← hq, hliftq, hu]
        simp [t.2]
  · refine ⟨by rw [hliftq]; exact hind, fun t ht => ?_⟩
    rw [hliftq]
    exact hxsV t ht

end NLQCLean.DirectVolume

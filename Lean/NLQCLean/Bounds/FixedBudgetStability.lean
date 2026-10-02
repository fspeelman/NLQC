import NLQCLean.Semialgebraic.PolynomialStability
import NLQCLean.Arithmetic.PhysicalPolynomialEncoding
import NLQCLean.Arithmetic.PhysicalScorePolynomial
import NLQCLean.Models.ChargedCompactProtocols
import NLQCLean.Exact.ExactBadDecomposition
import NLQCLean.Exact.FiniteOrbits
import NLQCLean.Exact.CompressionFiniteOrbits

/-!
# Fixed-budget stability (`cor:fixed-budget-stability`)

Fix `d ≥ 2` and `K ≥ 1` and suppose some unitary has an exact protocol of footprint at most
`K`. There are `C, α > 0` such that every `T ∈ Reach_{K,ε}` lies within normalized Frobenius
distance `C ε^α` of a unitary `S` with an exact protocol of footprint at most `K`.

In real coordinates `x` of the target, the least deficit is `1 - M(x)`, where `M` is the
maximum of the integer score polynomials `d⁻⁴ N_s(x, c)` over the finitely many charged
shapes `s` and the physical points `c` (the zero set of the integer constraint sum of
squares). `exists_stability_of_familyMax` (the semialgebraic Łojasiewicz inequality) gives
`|x - e|^{2n} ≤ C (1 - M x)` for some exact `e`.

The constants depend on `d` and `K`; nothing controls them as `K` grows.
-/

noncomputable section

namespace NLQCLean.FixedBudget

open Matrix MvPolynomial PhysicalPolynomial
open scoped Matrix.Norms.Frobenius

variable {d : ℕ}

/-- Real coordinates of a `d² × d²` complex matrix. -/
abbrev TIdx (d : ℕ) := (LogicalIndex d × LogicalIndex d) × Fin 2

/-- The complex matrix with the given real coordinates. -/
def matOf (x : TIdx d → ℝ) : Matrix (LogicalIndex d) (LogicalIndex d) ℂ :=
  coordinateMatrix id x

/-- The real coordinates of a matrix. -/
def coordsOf (U : Matrix (LogicalIndex d) (LogicalIndex d) ℂ) : TIdx d → ℝ :=
  complexRealCoordEquiv _ (fun q => U q.1 q.2)

theorem matOf_coordsOf (U : Matrix (LogicalIndex d) (LogicalIndex d) ℂ) :
    matOf (coordsOf U) = U := by
  ext p q
  apply Complex.ext <;> simp [matOf, coordsOf, coordinateMatrix, coordinateVector,
    complexRealCoordEquiv]

theorem coordsOf_matOf (x : TIdx d → ℝ) : coordsOf (matOf x) = x := by
  funext ⟨⟨p, q⟩, k⟩
  fin_cases k <;> simp [matOf, coordsOf, coordinateMatrix, coordinateVector,
    complexRealCoordEquiv]

theorem continuous_coordsOf :
    Continuous (coordsOf : Matrix (LogicalIndex d) (LogicalIndex d) ℂ → TIdx d → ℝ) := by
  refine continuous_pi fun ⟨⟨p, q⟩, k⟩ => ?_
  fin_cases k
  · exact Complex.continuous_re.comp (continuous_id.matrix_elem p q)
  · exact Complex.continuous_im.comp (continuous_id.matrix_elem p q)

/-- An integer polynomial with real coefficients. -/
def realPoly {σ : Type*} (p : MvPolynomial σ ℤ) : MvPolynomial σ ℝ :=
  MvPolynomial.map (Int.castRingHom ℝ) p

theorem eval_realPoly {σ : Type*} (x : σ → ℝ) (p : MvPolynomial σ ℤ) :
    MvPolynomial.eval x (realPoly p) = PhysicalPolynomial.eval x p := by
  rw [realPoly, MvPolynomial.eval_map]
  rfl

/-! ### The polynomial family -/

/-- The cardinalities of a charged shape. -/
def shp {K : ℕ} (s : ChargedShape d K) : Fin 8 → ℕ := fun i => (s.val i).val

/-- Physical points of a shape, in real coordinates. -/
def physPts {K : ℕ} (s : ChargedShape d K) : Set (PhysicalCoordinateIndex d (shp s) → ℝ) :=
  {c | MvPolynomial.eval c (realPoly (physicalConstraintSumSquares d (shp s))) = 0}

/-- The normalized score polynomial of a shape. -/
def scorePoly {K : ℕ} (s : ChargedShape d K) :
    MvPolynomial (TIdx d ⊕ PhysicalCoordinateIndex d (shp s)) ℝ :=
  MvPolynomial.C (((d : ℝ) ^ 4)⁻¹) * realPoly (physicalScoreNumeratorPolynomial d (shp s))

theorem mem_physPts_iff {K : ℕ} (s : ChargedShape d K) (p : PhysicalBlocks d (shp s)) :
    physicalCoordinatesEquiv d (shp s) p ∈ physPts s ↔ p ∈ physicalSet d (shp s) := by
  rw [physPts, Set.mem_ofPred_eq, eval_realPoly]
  exact physicalConstraintSumSquares_eval_coordinates_eq_zero_iff d _ p

theorem eval_scorePoly (hd : 0 < d) {K : ℕ} (s : ChargedShape d K) (x : TIdx d → ℝ)
    (p : PhysicalBlocks d (shp s)) :
    MvPolynomial.eval (Sum.elim x (physicalCoordinatesEquiv d (shp s) p)) (scorePoly s) =
      physicalScore (matOf x) p := by
  have h := physicalScoreNumeratorPolynomial_evaluate hd (shp s) (matOf x) p
  have hcoords : physicalScoreCoordinates d (shp s) (matOf x) p =
      Sum.elim x (physicalCoordinatesEquiv d (shp s) p) := by
    simp only [physicalScoreCoordinates]
    congr 1
    exact coordsOf_matOf x
  rw [hcoords] at h
  have hd4 : (d : ℝ) ^ 4 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hd.ne')
  rw [scorePoly, map_mul, MvPolynomial.eval_C, eval_realPoly, h, ← mul_assoc,
    inv_mul_cancel₀ hd4, one_mul]

theorem familyValues_eq (hd : 0 < d) (K : ℕ) (x : TIdx d → ℝ) :
    familyValues (fun s : ChargedShape d K => physPts s) (fun s => scorePoly s) x =
      chargedShapeScores (matOf x) K := by
  ext v
  simp only [familyValues, chargedShapeScores, shapeScores, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨s, c, hc, rfl⟩
    refine ⟨s, (physicalCoordinatesEquiv d (shp s)).symm c, ?_, ?_⟩
    · exact (mem_physPts_iff s _).mp (by rwa [LinearEquiv.apply_symm_apply])
    · have h := eval_scorePoly hd s x ((physicalCoordinatesEquiv d (shp s)).symm c)
      rw [LinearEquiv.apply_symm_apply] at h
      exact h.symm
  · rintro ⟨s, p, hp, rfl⟩
    exact ⟨s, physicalCoordinatesEquiv d (shp s) p, (mem_physPts_iff s p).mpr hp,
      eval_scorePoly hd s x p⟩

theorem familyMax_eq (hd : 0 < d) (K : ℕ) (x : TIdx d → ℝ) :
    familyMax (fun s : ChargedShape d K => physPts s) (fun s => scorePoly s) x =
      unitaryScoreMaximum (matOf x) K := by
  rw [familyMax, familyValues_eq hd]
  rfl

/-! ### The unitary domain -/

/-- Real coordinates of unitaries. -/
def unitaryCoords (d : ℕ) : Set (TIdx d → ℝ) := {x | IsIsometry (matOf x)}

theorem isCompact_unitaryCoords (d : ℕ) : IsCompact (unitaryCoords d) := by
  have h : unitaryCoords d =
      coordsOf '' {U : Matrix (LogicalIndex d) (LogicalIndex d) ℂ | IsIsometry U} := by
    ext x
    constructor
    · intro hx
      exact ⟨matOf x, hx, coordsOf_matOf x⟩
    · rintro ⟨U, hU, rfl⟩
      change IsIsometry (matOf (coordsOf U))
      rwa [matOf_coordsOf]
  rw [h]
  exact (isCompact_isometries _ _).image continuous_coordsOf

theorem saOn_unitaryCoords (d : ℕ) : SAOn (unitaryCoords d) := by
  classical
  have h := SAOn.fintype_iInter fun i : LogicalIndex d => SAOn.fintype_iInter fun j =>
    (SAOn.zero (realPoly (isometryRealConstraint (id : TIdx d → TIdx d) i j))).inter
      (SAOn.zero (realPoly (isometryImagConstraint (id : TIdx d → TIdx d) i j)))
  refine h.congr fun x => ?_
  simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_ofPred_eq, eval_realPoly]
  exact isometryConstraints_eval_eq_zero_iff (id : TIdx d → TIdx d) x

/-! ### Fixed-budget stability -/

theorem frobenius_norm_sub_eq (x e : TIdx d → ℝ) :
    ‖matOf x - matOf e‖ = (∑ i, (x i - e i) ^ 2) ^ (1 / 2 : ℝ) := by
  rw [Matrix.frobenius_norm_def]
  congr 1
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => ?_
  refine (Real.rpow_two _).trans ((Complex.sq_norm _).trans ?_)
  rw [Complex.normSq_apply]
  simp only [Matrix.sub_apply, matOf, coordinateMatrix, coordinateVector, Matrix.of_apply, id,
    Complex.sub_re, Complex.sub_im]
  ring

/-- **`cor:fixed-budget-stability`.** For `d ≥ 2`, `K ≥ 1` and a nonempty exact set
`E_{d,K} = Reach_{K,0}`, there are `C, α > 0` such that every `T ∈ Reach_{K,ε}` is within
normalized Frobenius distance `C ε^α` of some `S ∈ E_{d,K}`. -/
theorem exists_fixedBudget_stability {K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K)
    (hE : ∃ S : unitaryGroup (Fin d × Fin d) ℂ, S ∈ pureReachable d K 0) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ T ∈ pureReachable d K ε,
      ∃ S ∈ pureReachable d K 0,
        ‖(T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - S‖ / d ≤ C * ε ^ α := by
  classical
  have hd0 : 0 < d := by omega
  set P := fun s : ChargedShape d K => physPts s
  set N := fun s : ChargedShape d K => scorePoly s
  have hmax : ∀ x, familyMax P N x = unitaryScoreMaximum (matOf x) K := familyMax_eq hd0 K
  have hP : ∀ s, IsCompact (P s) := fun s => by
    have : P s = physicalCoordinatesEquiv d (shp s) '' physicalSet d (shp s) := by
      ext c
      constructor
      · intro hc
        refine ⟨(physicalCoordinatesEquiv d (shp s)).symm c, ?_, by simp⟩
        rw [← mem_physPts_iff, LinearEquiv.apply_symm_apply]
        exact hc
      · rintro ⟨p, hp, rfl⟩
        exact (mem_physPts_iff s p).mpr hp
    rw [this]
    exact (isCompact_physicalSet d _).image
      (physicalCoordinatesEquiv d (shp s)).toLinearMap.continuous_of_finiteDimensional
  have hPsa : ∀ s, SAOn (P s) := fun s => SAOn.zero _
  have hne : ∃ s, (P s).Nonempty := by
    obtain ⟨v, hv⟩ := chargedShapeScores_nonempty hd (1 : Matrix (Fin d × Fin d)
      (Fin d × Fin d) ℂ) hK
    obtain ⟨s, p, hp, -⟩ := Set.mem_iUnion.mp hv
    exact ⟨s, _, (mem_physPts_iff s p).mpr hp⟩
  have hle : ∀ x ∈ unitaryCoords d, familyMax P N x ≤ 1 := by
    intro x hx
    rw [hmax]
    have := (unitaryScoreDeficit_mem_Icc hd hK (matOf x) hx).1
    unfold unitaryScoreDeficit at this
    linarith
  have hreach : ∀ (T : unitaryGroup (Fin d × Fin d) ℂ) (ε : ℝ), T ∈ pureReachable d K ε ↔
      1 - ε ≤ familyMax P N (coordsOf (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) := by
    intro T ε
    rw [hmax, matOf_coordsOf]
    exact mem_pureReachable_iff_le_unitaryScoreMaximum hd hK T ε
  have hTcoords : ∀ T : unitaryGroup (Fin d × Fin d) ℂ,
      coordsOf (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ∈ unitaryCoords d := by
    intro T
    change IsIsometry (matOf (coordsOf _))
    rw [matOf_coordsOf]
    exact Matrix.mem_unitaryGroup_iff'.mp T.property
  have hEx : ∃ x ∈ unitaryCoords d, familyMax P N x = 1 := by
    obtain ⟨S, hS⟩ := hE
    refine ⟨_, hTcoords S, le_antisymm (hle _ (hTcoords S)) ?_⟩
    have := (hreach S 0).mp hS
    linarith
  obtain ⟨C, hC, n, hn, hstab⟩ := exists_stability_of_familyMax (isCompact_unitaryCoords d)
    (saOn_unitaryCoords d) hP hPsa hne hle hEx
  refine ⟨C ^ (1 / (2 * n : ℝ)), 1 / (2 * n : ℝ), by positivity, by positivity,
    fun ε hε T hT => ?_⟩
  set x := coordsOf (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) with hxdef
  obtain ⟨e, heD, he1, hbound⟩ := hstab x (hTcoords T)
  let S : unitaryGroup (Fin d × Fin d) ℂ := ⟨matOf e, Matrix.mem_unitaryGroup_iff'.mpr heD⟩
  have hSreach : S ∈ pureReachable d K 0 := by
    rw [hreach]
    change 1 - 0 ≤ familyMax P N (coordsOf (matOf e))
    rw [coordsOf_matOf, he1]
    norm_num
  refine ⟨S, hSreach, ?_⟩
  have hdef : 1 - familyMax P N x ≤ ε := by
    have := (hreach T ε).mp hT
    linarith
  set A := ∑ i, (x i - e i) ^ 2 with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hAn : A ^ n ≤ C * ε := hbound.trans (mul_le_mul_of_nonneg_left hdef hC.le)
  have hnorm : ‖(T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - S‖ = A ^ (1 / 2 : ℝ) := by
    have h := frobenius_norm_sub_eq x e
    rw [hxdef, matOf_coordsOf] at h
    exact h
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hA1 : A ≤ (C * ε) ^ (1 / (n : ℝ)) := by
    have h1 : A = (A ^ n) ^ (1 / (n : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hA0, mul_one_div_cancel hnr.ne', Real.rpow_one]
    rw [h1]
    exact Real.rpow_le_rpow (pow_nonneg hA0 n) hAn (by positivity)
  have hdist : ‖(T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - S‖ ≤
      C ^ (1 / (2 * n : ℝ)) * ε ^ (1 / (2 * n : ℝ)) := by
    rw [hnorm, ← Real.mul_rpow hC.le hε]
    calc A ^ (1 / 2 : ℝ) ≤ ((C * ε) ^ (1 / (n : ℝ))) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hA0 hA1 (by norm_num)
      _ = (C * ε) ^ (1 / (2 * n : ℝ)) := by
          rw [← Real.rpow_mul (by positivity)]
          congr 1
          field_simp
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  calc ‖(T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - S‖ / d
      ≤ ‖(T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - S‖ :=
        div_le_self (norm_nonneg _) hd1
    _ ≤ _ := hdist

/-! ### The exact set is a finite union of orbits -/

/-- The exact set `E_{d,K} = Reach_{K,0}`, as a set of matrices. -/
def exactSet (d K : ℕ) : Set (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
  {U | ∃ hU : U ∈ unitaryGroup (Fin d × Fin d) ℂ, (⟨U, hU⟩ : unitaryGroup _ ℂ) ∈ pureReachable d K 0}

theorem exactSet_eq_iUnion_exactTargets {K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K) :
    exactSet d K = ⋃ s : ChargedShape d K, exactTargets d (shp s) := by
  have : NeZero d := ⟨by omega⟩
  ext U
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨hU, hreach⟩
    have hU' : IsIsometry U := Matrix.mem_unitaryGroup_iff'.mp hU
    have hle := (mem_pureReachable_iff_le_unitaryScoreMaximum hd hK ⟨U, hU⟩ 0).mp hreach
    have hzero : unitaryScoreDeficit U K = 0 := by
      have := (unitaryScoreDeficit_mem_Icc hd hK U hU').1
      unfold unitaryScoreDeficit at this ⊢
      change 1 - 0 ≤ unitaryScoreMaximum U K at hle
      linarith
    obtain ⟨t₀, P, hP, hperf⟩ := (unitaryScoreDeficit_eq_zero_iff hd hK U hU').mp hzero
    obtain ⟨t, ht, hcharge, Q, -, hchan⟩ := P.exists_bounded_support_charged_fin_representative hd K hP
    let s : ChargedShape d K :=
      ⟨fun i => ⟨t i, Nat.lt_succ_of_le (ht i).2⟩, hcharge⟩
    have hQ : Q.PerformsUnitary U := by
      change Q.operationalChannel = adConj U
      rw [← hchan]
      exact hperf
    exact ⟨s, PureProtocol.mem_exactTargets t Q ⟨hU', Matrix.mem_unitaryGroup_iff.mp hU⟩ hQ⟩
  · rintro ⟨s, hs⟩
    have hUt := unitaryTarget_of_mem_exactTargets hs
    obtain ⟨z, hz, rfl⟩ := hs
    let P := targetExactWitnessProtocol (shp s) hz
    have hperf := targetExactWitnessProtocol_performsUnitary (shp s) hz
    refine ⟨Matrix.mem_unitaryGroup_iff'.mpr hUt.conjTranspose_mul_self, shp s, P,
      FinProtocol.hasFootprint_of_support_charge (s := shp s) P s.property, ?_⟩
    change 1 - 0 ≤ scoreU z.1 P.operationalChannel
    rw [hperf, scoreU_adConj_self hUt.conjTranspose_mul_self]
    norm_num

/-- **`cor:fixed-budget-stability`, orbit part.** The exact set `E_{d,K}` is a finite union of
local-equivalence orbits of its own members. -/
theorem exists_exactSet_eq_iUnion_orbits {K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K) :
    ∃ R : Finset (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ), (∀ U ∈ R, U ∈ exactSet d K) ∧
      exactSet d K = ⋃ U ∈ R, unitaryDoubleOrbit (Fin d) (Fin d) U := by
  classical
  choose R hR hReq using fun s : ChargedShape d K => exists_finset_exactTargets_eq_iUnion_orbits d (shp s)
  rw [exactSet_eq_iUnion_exactTargets hd hK]
  refine ⟨Finset.univ.biUnion R, fun U hU => ?_, ?_⟩
  · obtain ⟨s, -, hUs⟩ := Finset.mem_biUnion.mp hU
    exact Set.mem_iUnion.mpr ⟨s, hR s U hUs⟩
  · ext V
    simp only [Set.mem_iUnion, Finset.mem_biUnion, Finset.mem_univ, true_and, exists_prop]
    constructor
    · rintro ⟨s, hV⟩
      rw [hReq s] at hV
      simp only [Set.mem_iUnion, exists_prop] at hV
      obtain ⟨U, hU, hVU⟩ := hV
      exact ⟨U, ⟨s, hU⟩, hVU⟩
    · rintro ⟨U, ⟨s, hU⟩, hVU⟩
      refine ⟨s, ?_⟩
      rw [hReq s]
      exact Set.mem_biUnion hU hVU

end NLQCLean.FixedBudget

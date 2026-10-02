import NLQCLean.Bounds.FixedBudgetStability
import NLQCLean.Arithmetic.PVMScorePolynomial
import NLQCLean.Models.ChargedCompactPVMProtocols
import NLQCLean.Exact.PVMBadDecomposition
import NLQCLean.Exact.PVMFiniteOrbits

/-!
# Fixed-budget stability for measurement targets

`cor:fixed-budget-stability` for PVMs, represented by their basis unitaries `M`: if some basis
has an exact two-sided protocol of footprint at most `K`, every `M ∈ Reach^{PVM}_{K,ε}` lies
within normalized Frobenius distance `C ε^α` of an exactly implementable basis, and the exact
set is a finite union of basis orbits. The proof is the unitary one with the integer PVM score
polynomial `pvmScoreNumeratorPolynomial`.
-/

noncomputable section

namespace NLQCLean.FixedBudget

open Matrix MvPolynomial PhysicalPolynomial
open scoped Matrix.Norms.Frobenius

variable {d : ℕ}

def shpP {K : ℕ} (s : ChargedPVMShape d K) : Fin 8 → ℕ := fun i => (s.val i).val

def physPtsP {K : ℕ} (s : ChargedPVMShape d K) : Set (PVMCoordinateIndex d (shpP s) → ℝ) :=
  {c | MvPolynomial.eval c (realPoly (pvmConstraintSumSquares d (shpP s))) = 0}

def scorePolyP {K : ℕ} (s : ChargedPVMShape d K) :
    MvPolynomial (TIdx d ⊕ PVMCoordinateIndex d (shpP s)) ℝ :=
  MvPolynomial.C (((d : ℝ) ^ 2)⁻¹) * realPoly (pvmScoreNumeratorPolynomial d (shpP s))

theorem mem_physPtsP_iff {K : ℕ} (s : ChargedPVMShape d K) (p : PVMPhysicalBlocks d (shpP s)) :
    pvmCoordinatesEquiv d (shpP s) p ∈ physPtsP s ↔ p ∈ pvmPhysicalSet d (shpP s) := by
  rw [physPtsP, Set.mem_ofPred_eq, eval_realPoly]
  exact pvmConstraintSumSquares_eval_coordinates_eq_zero_iff p

theorem eval_scorePolyP (hd : 0 < d) {K : ℕ} (s : ChargedPVMShape d K) (x : TIdx d → ℝ)
    (p : PVMPhysicalBlocks d (shpP s)) :
    MvPolynomial.eval (Sum.elim x (pvmCoordinatesEquiv d (shpP s) p)) (scorePolyP s) =
      pvmPhysicalScore (matOf x) p := by
  have h := pvmScoreNumeratorPolynomial_evaluate (matOf x) p
  have hcoords : pvmScoreCoordinates (matOf x) p =
      Sum.elim x (pvmCoordinatesEquiv d (shpP s) p) := by
    simp only [pvmScoreCoordinates]
    congr 1
    exact coordsOf_matOf x
  rw [hcoords] at h
  have hd2 : (d : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hd.ne')
  rw [scorePolyP, map_mul, MvPolynomial.eval_C, eval_realPoly, h, ← mul_assoc,
    inv_mul_cancel₀ hd2, one_mul]

theorem familyMaxP_eq (hd : 0 < d) (K : ℕ) (x : TIdx d → ℝ) :
    familyMax (fun s : ChargedPVMShape d K => physPtsP s) (fun s => scorePolyP s) x =
      pvmScoreMaximum (matOf x) K := by
  rw [familyMax]
  congr 1
  ext v
  simp only [familyValues, chargedPVMShapeScores, pvmShapeScores, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨s, c, hc, rfl⟩
    refine ⟨s, (pvmCoordinatesEquiv d (shpP s)).symm c, ?_, ?_⟩
    · exact (mem_physPtsP_iff s _).mp (by rwa [LinearEquiv.apply_symm_apply])
    · have h := eval_scorePolyP hd s x ((pvmCoordinatesEquiv d (shpP s)).symm c)
      rw [LinearEquiv.apply_symm_apply] at h
      exact h.symm
  · rintro ⟨s, p, hp, rfl⟩
    exact ⟨s, pvmCoordinatesEquiv d (shpP s) p, (mem_physPtsP_iff s p).mpr hp,
      eval_scorePolyP hd s x p⟩

/-- **`cor:fixed-budget-stability`, measurement targets.** -/
theorem exists_fixedBudget_stability_pvm {K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K)
    (hE : ∃ S : unitaryGroup (Fin d × Fin d) ℂ, S ∈ purePVMReachable d K 0) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ T ∈ purePVMReachable d K ε,
      ∃ S ∈ purePVMReachable d K 0,
        ‖(T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - S‖ / d ≤ C * ε ^ α := by
  classical
  have hd0 : 0 < d := by omega
  set P := fun s : ChargedPVMShape d K => physPtsP s
  set N := fun s : ChargedPVMShape d K => scorePolyP s
  have hmax : ∀ x, familyMax P N x = pvmScoreMaximum (matOf x) K := familyMaxP_eq hd0 K
  have hP : ∀ s, IsCompact (P s) := fun s => by
    have : P s = pvmCoordinatesEquiv d (shpP s) '' pvmPhysicalSet d (shpP s) := by
      ext c
      constructor
      · intro hc
        refine ⟨(pvmCoordinatesEquiv d (shpP s)).symm c, ?_, by simp⟩
        exact (mem_physPtsP_iff s _).mp (by rwa [LinearEquiv.apply_symm_apply])
      · rintro ⟨p, hp, rfl⟩
        exact (mem_physPtsP_iff s p).mpr hp
    rw [this]
    exact (isCompact_pvmPhysicalSet d _).image
      (pvmCoordinatesEquiv d (shpP s)).toLinearMap.continuous_of_finiteDimensional
  have hPsa : ∀ s, SAOn (P s) := fun s => SAOn.zero _
  have hne : ∃ s, (P s).Nonempty := by
    obtain ⟨v, hv⟩ := chargedPVMShapeScores_nonempty hd
      (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) hK
    obtain ⟨s, p, hp, -⟩ := Set.mem_iUnion.mp hv
    exact ⟨s, _, (mem_physPtsP_iff s p).mpr hp⟩
  have hle : ∀ x ∈ unitaryCoords d, familyMax P N x ≤ 1 := by
    intro x hx
    rw [hmax]
    have := (pvmScoreDeficit_mem_Icc hd hK (matOf x) hx).1
    unfold pvmScoreDeficit at this
    linarith
  have hreach : ∀ (T : unitaryGroup (Fin d × Fin d) ℂ) (ε : ℝ), T ∈ purePVMReachable d K ε ↔
      1 - ε ≤ familyMax P N (coordsOf (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) := by
    intro T ε
    rw [hmax, matOf_coordsOf]
    exact mem_purePVMReachable_iff_le_pvmScoreMaximum hd hK T ε
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
  have hSreach : S ∈ purePVMReachable d K 0 := by
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

/-- The exact measurement set `E^{PVM}_{d,K}`, as a set of basis matrices. -/
def pvmExactSet (d K : ℕ) : Set (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
  {M | ∃ hM : M ∈ unitaryGroup (Fin d × Fin d) ℂ,
    (⟨M, hM⟩ : unitaryGroup _ ℂ) ∈ purePVMReachable d K 0}

theorem pvmExactSet_eq_iUnion {K : ℕ} (hd : 2 ≤ d) :
    pvmExactSet d K = ⋃ s : ChargedPVMShape d K, pvmExactTargets d (shpP s) := by
  have : NeZero d := ⟨by omega⟩
  ext M
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨hM, t, P, hP, hs⟩
    have hMi : IsIsometry M := Matrix.mem_unitaryGroup_iff'.mp hM
    obtain ⟨u, hu, hcharge, Q, hchan⟩ := P.exists_bounded_support_charged_fin_pvm_representative hd K hP
    have hone : scorePVM M Q.operationalChannel = 1 := by
      rw [← hchan]
      have hle := (P.scorePVM_mem_Icc hMi).2
      change 1 - 0 ≤ scorePVM M P.operationalChannel at hs
      linarith
    let s : ChargedPVMShape d K := ⟨fun i => ⟨u i, Nat.lt_succ_of_le (hu i)⟩, hcharge⟩
    refine ⟨s, ?_⟩
    rw [pvmExactTargets_eq_protocols]
    exact ⟨hM, Q, (Q.scorePVM_eq_one_iff_performsPVM hMi).mp hone⟩
  · rintro ⟨s, hs⟩
    rw [pvmExactTargets_eq_protocols] at hs
    obtain ⟨hM, Q, hQ⟩ := hs
    refine ⟨hM, shpP s, Q, FinPVMProtocol.hasFootprint_of_support_charge (s := shpP s) Q s.property,
      ?_⟩
    have hone := (Q.scorePVM_eq_one_iff_performsPVM (Matrix.mem_unitaryGroup_iff'.mp hM)).mpr hQ
    change 1 - 0 ≤ scorePVM M Q.operationalChannel
    rw [hone]
    norm_num

/-- **`cor:fixed-budget-stability`, orbit part, measurement targets.** -/
theorem exists_pvmExactSet_eq_iUnion_orbits {K : ℕ} (hd : 2 ≤ d) :
    ∃ R : Finset (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ), (∀ M ∈ R, M ∈ pvmExactSet d K) ∧
      pvmExactSet d K = ⋃ M ∈ R, pvmBasisOrbit (Fin d) (Fin d) M := by
  classical
  choose R hR hReq using fun s : ChargedPVMShape d K =>
    exists_finset_pvmExactTargets_eq_iUnion_orbits d (shpP s)
  rw [pvmExactSet_eq_iUnion hd]
  refine ⟨Finset.univ.biUnion R, fun M hM => ?_, ?_⟩
  · obtain ⟨s, -, hMs⟩ := Finset.mem_biUnion.mp hM
    exact Set.mem_iUnion.mpr ⟨s, hR s M hMs⟩
  · ext V
    simp only [Set.mem_iUnion, Finset.mem_biUnion, Finset.mem_univ, true_and, exists_prop]
    constructor
    · rintro ⟨s, hV⟩
      rw [hReq s] at hV
      simp only [Set.mem_iUnion, exists_prop] at hV
      obtain ⟨M, hM, hVM⟩ := hV
      exact ⟨M, ⟨s, hM⟩, hVM⟩
    · rintro ⟨M, ⟨s, hM⟩, hVM⟩
      refine ⟨s, ?_⟩
      rw [hReq s]
      exact Set.mem_biUnion hM hVM

end NLQCLean.FixedBudget

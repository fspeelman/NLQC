import NLQCLean.Approx.PVMExtendedWitness
import NLQCLean.Approx.PVMPolynomialCoverage

/-!
# Fixed-format cubic PVM witness map

The blockwise extension has coordinate degree
at most eighteen and agrees with the raw overlap on the exact eight-constraint
source. Its full ambient derivative norm obeys the fixed coordinate budget.

-/

namespace NLQCLean
open Matrix
open scoped Matrix.Norms.Frobenius

namespace PVMReverseBlocks
variable {a d K D : ℕ} {s : PVMReverseShape d K}

namespace PolynomialDegreeLE
variable {f : RealEuclidean a → PVMReverseBlocks s}

theorem cubic (hf : PolynomialDegreeLE D f) :
    PolynomialDegreeLE (3 * D) (fun x => normalizedCubicBlocks (f x)) :=
  ⟨polynomialDegree_cubicSphere hf.1,
    fun i => polynomialDegree_rescaledCubicSphere (hf.2.1 i) _,
    hf.2.2.1.rescaledCubicStiefel _, hf.2.2.2.1.rescaledCubicStiefel _,
    hf.2.2.2.2.1.rescaledCubicStiefel _, hf.2.2.2.2.2.rescaledCubicStiefel _⟩
end PolynomialDegreeLE

variable (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K)

theorem polynomialDegree_extendedOverlap :
    MatrixPolynomialDegreeLE 18 (fun x => extendedOverlap (decodeCoordinates s hd hfloor x)) :=
  (PolynomialDegreeLE.linear (decodeCoordinates s hd hfloor)).cubic.rescale.overlap

theorem polynomialDegree_coordinateOverlap (j : Fin (2 * d ^ 4)) :
    RealPolynomialDegreeLE 18 (fun x => coordinateOverlap s hd hfloor x j) :=
  polynomialDegree_overlapOutputCoordinates (polynomialDegree_extendedOverlap s hd hfloor) j

/-- The globally defined cubic overlap map in the fixed polynomial format. -/
noncomputable def coordinateOverlapPolynomial :
    BoundedPolynomialMap (pvmWitnessCoordinateBudget d K) (2 * d ^ 4) where
  coordinates j := Classical.choose (polynomialDegree_coordinateOverlap s hd hfloor j)
  degree_le j := (Classical.choose_spec (polynomialDegree_coordinateOverlap s hd hfloor j)).1.trans (by decide)

theorem coordinateOverlapPolynomial_degree_le (j : Fin (2 * d ^ 4)) :
    ((coordinateOverlapPolynomial s hd hfloor).coordinates j).totalDegree ≤ 18 :=
  (Classical.choose_spec (polynomialDegree_coordinateOverlap s hd hfloor j)).1

theorem coordinateOverlapPolynomial_eval (x : RealEuclidean (pvmWitnessCoordinateBudget d K)) :
    (coordinateOverlapPolynomial s hd hfloor).eval x = coordinateOverlap s hd hfloor x := by
  ext j
  exact (Classical.choose_spec (polynomialDegree_coordinateOverlap s hd hfloor j)).2 x

theorem coordinateOverlapPolynomial_eq_raw_of_mem {δ : ℝ}
    {x : RealEuclidean (pvmWitnessCoordinateBudget d K)}
    (hx : x ∈ (witnessFormat s hd hfloor δ).source) :
    (coordinateOverlapPolynomial s hd hfloor).eval x =
      (coordinateRawOverlapPolynomial s hd hfloor).eval x := by
  rw [coordinateOverlapPolynomial_eval, coordinateRawOverlapPolynomial_eval]
  exact coordinateOverlap_eq_raw s hd hfloor ((mem_witnessFormat_source_iff s hd hfloor δ x).mp hx).1

/-- The geometry map's ambient derivative obeys the budget at every
point of its exact polynomial source. -/
theorem witnessFormat_ambient_norm_le (hd2 : 2 ≤ d) {δ : ℝ}
    {x : RealEuclidean (pvmWitnessCoordinateBudget d K)}
    (hx : x ∈ (witnessFormat s hd hfloor δ).source) :
    ‖fderiv ℝ (coordinateOverlapPolynomial s hd hfloor).eval x‖ ≤
      (pvmWitnessCoordinateBudget d K : ℝ) := by
  have he : (coordinateOverlapPolynomial s hd hfloor).eval = coordinateOverlap s hd hfloor :=
    funext (coordinateOverlapPolynomial_eval s hd hfloor)
  rw [he]
  exact norm_fderiv_coordinateOverlap_le_budget s hd hfloor hd2
    ((mem_witnessFormat_source_iff s hd hfloor δ x).mp hx).1

/-- Raw witnesses enter the same source and are unchanged by the cubic. -/
theorem exists_mem_extended_witnessFormat_source (δ : ℝ) {x : PVMReverseBlocks s}
    (hx : IsValid x) (hdef : (d : ℝ) ^ 2 - ‖overlap x‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2) :
    ∃ y ∈ (witnessFormat s hd hfloor δ).source,
      (coordinateOverlapPolynomial s hd hfloor).eval y = overlapOutputCoordinates d (overlap x) := by
  obtain ⟨y, hy, he⟩ := exists_mem_witnessFormat_source s hd hfloor δ hx hdef
  exact ⟨y, hy, (coordinateOverlapPolynomial_eq_raw_of_mem s hd hfloor hy).trans he⟩

end PVMReverseBlocks

section PhysicalCoverage

variable {d : ℕ} {ρA ρB κA κB μA μB eA eB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype eA] [Fintype eB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq eA] [DecidableEq eB]

/-- The physical cover also uses the cubic polynomial map, without extra premises. -/
theorem PureProtocol.exists_pvm_extended_polynomial_witness
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      (Fin d × Fin d) (Fin d × Fin d) eA eB)
    (hd : 0 < d) {K : ℕ} {ε : ℝ}
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : IsIsometry M) (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hε : 0 ≤ ε ∧ ε ≤ 1 / 2)
    (hscore : 1 - ε ≤ scorePVM M P.operationalChannel) :
    ∃ hfloor : d ^ 2 ≤ 4 * K, ∃ s : PVMReverseShape d K,
      ∃ y ∈ (PVMReverseBlocks.witnessFormat s hd hfloor (2 * Real.sqrt ε)).source,
        ‖(PVMReverseBlocks.coordinateOverlapPolynomial s hd hfloor).eval y -
            overlapOutputCoordinates d Mᴴ‖ ≤ 2 * (d : ℝ) * Real.sqrt ε := by
  obtain ⟨hfloor, s, y, hy, he⟩ := P.exists_pvm_polynomial_witness hd M hM hK hε hscore
  refine ⟨hfloor, s, y, hy, ?_⟩
  rw [PVMReverseBlocks.coordinateOverlapPolynomial_eq_raw_of_mem s hd hfloor hy]
  exact he

/-- The physical cover also uses the cubic polynomial map, without extra premises. -/
theorem MixedResource.exists_pvm_extended_polynomial_witness
    {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix ((Fin d × Fin d) × eA) (κA × μB) ℂ)
    (DB : Matrix ((Fin d × Fin d) × eB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (hd : 0 < d) {K R : ℕ} {ε : ℝ}
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hM : IsIsometry M)
    (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    (hε : 0 ≤ ε ∧ ε ≤ 1 / 2)
    (hscore : 1 - ε ≤ scorePVM M (m.mixedChannel VA VB DA DB)) :
    ∃ hfloor : d ^ 2 ≤ 4 * K, ∃ s : PVMReverseShape d K,
      ∃ y ∈ (PVMReverseBlocks.witnessFormat s hd hfloor (2 * Real.sqrt ε)).source,
        ‖(PVMReverseBlocks.coordinateOverlapPolynomial s hd hfloor).eval y -
            overlapOutputCoordinates d Mᴴ‖ ≤ 2 * (d : ℝ) * Real.sqrt ε := by
  obtain ⟨hfloor, s, y, hy, he⟩ := m.exists_pvm_polynomial_witness VA VB DA DB hVA hVB hDA hDB hd M hM hR hK hε hscore
  refine ⟨hfloor, s, y, hy, ?_⟩
  rw [PVMReverseBlocks.coordinateOverlapPolynomial_eq_raw_of_mem s hd hfloor hy]
  exact he

end PhysicalCoverage
end NLQCLean

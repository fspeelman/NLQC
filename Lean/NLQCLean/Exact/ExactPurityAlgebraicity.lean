import NLQCLean.Exact.TargetWitnessPolynomial
import NLQCLean.Arithmetic.RationalIntegerPolynomials
import NLQCLean.Arithmetic.RationalSemialgebraicBoundary

/-!
# Algebraicity of exact finite-architecture purity values

For each finite architecture separately, the actual exact-witness equations
have integer coefficients and the normalized target purity has rational
coefficients. Proved rational projection supplies its rational scalar image.
Scalar Sard makes that same image null, so each value is algebraic. Membership
in the countable union is handled one architecture at a time; no rational sign
description of the entire union is asserted.
-/

noncomputable section

namespace NLQCLean

open MeasureTheory
open ExactWitnessCoordinates ExactWitnessPolynomial

/-- The actual target-witness locus in raw Euclidean coordinates. -/
def exactWitnessCoordinateSet (d : ℕ) (s : ForwardShape) :
    Set (RealEuclidean (coordinateCount d s)) :=
  {x | (coordinatesEquiv d s).symm (fun i => x i) ∈ targetExactWitnessSet d s}

/-- Four integer equations describe precisely the physical and frozen locus. -/
theorem rationalSemialgebraic_exactWitnessCoordinateSet (d : ℕ) (s : ForwardShape) :
    RationalSemialgebraic (exactWitnessCoordinateSet d s) := by
  have h := RationalSemialgebraic.iInter
    (fun i : Fin 4 => {x : RealEuclidean (coordinateCount d s) |
      PhysicalPolynomial.eval (fun j => x j) (targetConstraintPolynomial d s i) = 0})
    (fun i => RationalSemialgebraic.polynomial_zero_int (targetConstraintPolynomial d s i))
  convert h using 1
  ext x
  simp only [exactWitnessCoordinateSet, Set.mem_ofPred_eq, Set.mem_iInter]
  exact (targetConstraintPolynomial_eval_eq_zero_iff d s (fun j => x j)).symm

/-- The one-coordinate normalized target-purity polynomial map. -/
def exactWitnessPurityMap (d : ℕ) (s : ForwardShape) :
    RealEuclidean (coordinateCount d s) → RealEuclidean 1 :=
  PolynomialSignDNF.polynomialMap
    (fun _ => MvPolynomial.map (algebraMap ℚ ℝ) (targetPurityPolynomial d s))

theorem exactWitnessPurityMap_apply (d : ℕ) (s : ForwardShape)
    (x : RealEuclidean (coordinateCount d s)) (i : Fin 1) :
    exactWitnessPurityMap d s x i =
      purity ((d : ℝ) ^ 4)⁻¹ ((coordinatesEquiv d s).symm (fun j => x j)).1 := by
  change MvPolynomial.eval (fun j => x j)
    (MvPolynomial.map (algebraMap ℚ ℝ) (targetPurityPolynomial d s)) = _
  rw [MvPolynomial.eval_map]
  exact targetPurityPolynomial_evaluate d s (fun j => x j)

/-- The rational polynomial image agrees with the original critical image. -/
theorem exactWitnessPurityMap_image (d : ℕ) (s : ForwardShape) :
    exactWitnessPurityMap d s '' exactWitnessCoordinateSet d s =
      {y : RealEuclidean 1 | y 0 ∈
        scalarPhi ((d : ℝ) ^ 4)⁻¹ '' {x : ShapeBlocks d s | IsExactWitness x}} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_ofPred_eq, exactWitnessPurityMap_apply]
    rw [← purity_image_targetExactWitnessSet d s ((d : ℝ) ^ 4)⁻¹]
    exact ⟨(coordinatesEquiv d s).symm (fun j => x j), hx, rfl⟩
  · intro hy
    rw [Set.mem_ofPred_eq, ← purity_image_targetExactWitnessSet d s ((d : ℝ) ^ 4)⁻¹] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    refine ⟨WithLp.toLp 2 (coordinatesEquiv d s z), ?_, ?_⟩
    · change (coordinatesEquiv d s).symm (coordinatesEquiv d s z) ∈ targetExactWitnessSet d s
      simpa only [LinearEquiv.symm_apply_apply] using hz
    · ext i
      rw [exactWitnessPurityMap_apply]
      change purity ((d : ℝ) ^ 4)⁻¹
        ((coordinatesEquiv d s).symm (coordinatesEquiv d s z)).1 = y i
      simpa only [LinearEquiv.symm_apply_apply,
        show i = (0 : Fin 1) from Subsingleton.elim _ _] using hzy

/-- Rationality is proved for each actual finite-shape image. -/
theorem rationalSemialgebraic_shapePurityValues (d : ℕ) (s : ForwardShape) :
    RationalSemialgebraic {y : RealEuclidean 1 | y 0 ∈
      scalarPhi ((d : ℝ) ^ 4)⁻¹ '' {x : ShapeBlocks d s | IsExactWitness x}} := by
  rw [← exactWitnessPurityMap_image]
  exact (rationalSemialgebraic_exactWitnessCoordinateSet d s).polynomial_image_rat
    (fun _ : Fin 1 => targetPurityPolynomial d s)

/-- Every exact purity value of a fixed architecture is algebraic over ℚ. -/
theorem isAlgebraic_of_mem_shapePurityValues (d : ℕ) (s : ForwardShape)
    {t : ℝ}
    (ht : t ∈ scalarPhi ((d : ℝ) ^ 4)⁻¹ '' {x : ShapeBlocks d s | IsExactWitness x}) :
    IsAlgebraic ℚ t := by
  have h := rationalSemialgebraic_shapePurityValues d s
  apply h.isAlgebraic_of_scalar_measure_eq_zero
  · change volume (scalarPhi ((d : ℝ) ^ 4)⁻¹ '' {x : ShapeBlocks d s | IsExactWitness x}) = 0
    exact volume_scalarPhi_image_eq_zero ((d : ℝ) ^ 4)⁻¹
      {x : ShapeBlocks d s | IsExactWitness x} (fun _ hx => hx)
  · exact ht

/-- All finite architectures are covered without a rationality claim for
 their countable union. -/
theorem isAlgebraic_of_mem_exactPurityValues (d : ℕ) {t : ℝ}
    (ht : t ∈ exactPurityValues d) : IsAlgebraic ℚ t := by
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp ht
  exact isAlgebraic_of_mem_shapePurityValues d s hs

/-- The same values admit nonzero integer annihilating polynomials. -/
theorem isAlgebraic_int_of_mem_exactPurityValues (d : ℕ) {t : ℝ}
    (ht : t ∈ exactPurityValues d) : IsAlgebraic ℤ t :=
  (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr (isAlgebraic_of_mem_exactPurityValues d ht)

end NLQCLean

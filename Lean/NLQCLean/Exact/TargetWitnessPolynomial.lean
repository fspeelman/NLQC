import NLQCLean.Exact.TargetWitness
import NLQCLean.Exact.WitnessRationalCoordinates
import NLQCLean.Arithmetic.ComplexMatrixPolynomials
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Integer polynomial equations for exact target witnesses

The target, environment witness and five physical blocks remain independent
variables. Four explicit integer equations encode precisely physicality,
witness normalization, target coisometry and the actual frozen-dilation
identity. The normalized target purity is a constructed rational polynomial.
-/

noncomputable section

namespace NLQCLean.PhysicalPolynomial.ComplexPair

attribute [local implicit_reducible] Matrix

/-- Insertion of a variable environment vector in the system-then-environment grouping. -/
def vectorInsert {σ ε : Type*} (κ : Type*) [DecidableEq κ]
    (entry : ε × Fin 2 → σ) : Matrix (κ × ε) κ (ComplexPair σ) :=
  Matrix.of fun p k => if p.1 = k then
    coordinatePair (entry (p.2, 0)) (entry (p.2, 1)) else (0, 0)

@[simp] theorem evaluateMatrix_vectorInsert {σ κ ε : Type*} [DecidableEq κ]
    (z : σ → ℝ) (entry : ε × Fin 2 → σ) :
    evaluateMatrix z (vectorInsert κ entry) =
      NLQCLean.insertVector κ (PhysicalPolynomial.coordinateVector entry z) := by
  ext p k
  by_cases hpk : p.1 = k <;>
    simp [evaluateMatrix, vectorInsert, NLQCLean.insertVector_apply, hpk,
      PhysicalPolynomial.coordinateVector]

end NLQCLean.PhysicalPolynomial.ComplexPair

namespace NLQCLean.ExactWitnessPolynomial

attribute [local implicit_reducible] Matrix

open Matrix
open PhysicalPolynomial
open scoped Kronecker

/-- The independent target block as a matrix of integer polynomial pairs. -/
def targetPolynomial (d : ℕ) (s : ForwardShape) :
    Matrix (Fin d × Fin d) (Fin d × Fin d)
      (ComplexPair (Fin (ExactWitnessCoordinates.coordinateCount d s))) :=
  ComplexPair.matrixVariable (ExactWitnessCoordinates.targetCoordinates d s)

@[simp] theorem targetPolynomial_evaluate (d : ℕ) (s : ForwardShape)
    (z : Fin (ExactWitnessCoordinates.coordinateCount d s) → ℝ) :
    ComplexPair.evaluateMatrix z (targetPolynomial d s) =
      ((ExactWitnessCoordinates.coordinatesEquiv d s).symm z).1 := by
  simp only [targetPolynomial, ComplexPair.evaluateMatrix_matrixVariable,
    ExactWitnessCoordinates.coordinateMatrix_targetCoordinates]

/-- The independent environment insertion polynomial. -/
def witnessInsertPolynomial (d : ℕ) (s : ForwardShape) :
    Matrix ((Fin d × Fin d) × ExactWitnessCoordinates.WitnessEnvironmentIndex s)
      (Fin d × Fin d) (ComplexPair (Fin (ExactWitnessCoordinates.coordinateCount d s))) :=
  ComplexPair.vectorInsert (Fin d × Fin d) (ExactWitnessCoordinates.witnessCoordinates d s)

@[simp] theorem witnessInsertPolynomial_evaluate (d : ℕ) (s : ForwardShape)
    (z : Fin (ExactWitnessCoordinates.coordinateCount d s) → ℝ) :
    ComplexPair.evaluateMatrix z (witnessInsertPolynomial d s) =
      insertVector (Fin d × Fin d) ((ExactWitnessCoordinates.coordinatesEquiv d s).symm z).2.2.1 := by
  simp only [witnessInsertPolynomial, ComplexPair.evaluateMatrix_vectorInsert,
    ExactWitnessCoordinates.coordinateVector_witnessCoordinates]

/-- The production global matrix, assembled with its original exchange and output regrouping. -/
def globalPolynomial (d : ℕ) (s : ForwardShape) :
    Matrix ((Fin d × Fin d) × ExactWitnessCoordinates.WitnessEnvironmentIndex s)
      (Fin d × Fin d) (ComplexPair (Fin (ExactWitnessCoordinates.coordinateCount d s))) :=
  let VA := ComplexPair.matrixVariable (ExactWitnessCoordinates.encoderACoordinates d s)
  let VB := ComplexPair.matrixVariable (ExactWitnessCoordinates.encoderBCoordinates d s)
  let DA := ComplexPair.matrixVariable (ExactWitnessCoordinates.decoderACoordinates d s)
  let DB := ComplexPair.matrixVariable (ExactWitnessCoordinates.decoderBCoordinates d s)
  let J := ComplexPair.resourceInsert (ιA := Fin d) (ιB := Fin d)
    (ExactWitnessCoordinates.resourceCoordinates d s)
  let encoded := ComplexPair.matrixMultiply (ComplexPair.matrixKronecker VA VB) J
  let exchanged := encoded.submatrix
    (exchangeEquiv (Fin (s 2)) (Fin (s 4)) (Fin (s 3)) (Fin (s 5))) id
  let joint := ComplexPair.matrixMultiply (ComplexPair.matrixKronecker DA DB) exchanged
  joint.submatrix (outputRegroup (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7))) id

@[simp] theorem globalPolynomial_evaluate (d : ℕ) (s : ForwardShape)
    (z : Fin (ExactWitnessCoordinates.coordinateCount d s) → ℝ) :
    ComplexPair.evaluateMatrix z (globalPolynomial d s) =
      globalIsometryRegrouped
        ((ExactWitnessCoordinates.coordinatesEquiv d s).symm z).2.1
        ((ExactWitnessCoordinates.coordinatesEquiv d s).symm z).2.2.2.1
        ((ExactWitnessCoordinates.coordinatesEquiv d s).symm z).2.2.2.2.1
        ((ExactWitnessCoordinates.coordinatesEquiv d s).symm z).2.2.2.2.2.1
        ((ExactWitnessCoordinates.coordinatesEquiv d s).symm z).2.2.2.2.2.2 := by
  simp only [globalPolynomial, ComplexPair.evaluateMatrix_submatrix,
    ComplexPair.evaluateMatrix_matrixMultiply, ComplexPair.evaluateMatrix_matrixKronecker,
    ComplexPair.evaluateMatrix_matrixVariable, ComplexPair.evaluateMatrix_resourceInsert,
    ExactWitnessCoordinates.coordinateMatrix_encoderACoordinates,
    ExactWitnessCoordinates.coordinateMatrix_encoderBCoordinates,
    ExactWitnessCoordinates.coordinateMatrix_decoderACoordinates,
    ExactWitnessCoordinates.coordinateMatrix_decoderBCoordinates,
    ExactWitnessCoordinates.coordinateVector_resourceCoordinates]
  rw [← exchangeMatrix_mul]
  rfl

/-- Reuse the existing five-block physical equations by renaming their variables. -/
def targetPhysicalConstraintPolynomial (d : ℕ) (s : ForwardShape) :
    MvPolynomial (Fin (ExactWitnessCoordinates.coordinateCount d s)) ℤ :=
  MvPolynomial.rename (ExactWitnessCoordinates.liftPhysicalCoordinates d s)
    (physicalConstraintSumSquares d s)

theorem targetPhysicalConstraintPolynomial_eval_eq_zero_iff (d : ℕ) (s : ForwardShape)
    (z : Fin (ExactWitnessCoordinates.coordinateCount d s) → ℝ) :
    PhysicalPolynomial.eval z (targetPhysicalConstraintPolynomial d s) = 0 ↔
      ExactWitnessCoordinates.physicalBlocks
        ((ExactWitnessCoordinates.coordinatesEquiv d s).symm z).2 ∈ physicalSet d s := by
  unfold targetPhysicalConstraintPolynomial
  change MvPolynomial.eval₂Hom (Int.castRingHom ℝ) z
      (MvPolynomial.rename (ExactWitnessCoordinates.liftPhysicalCoordinates d s)
        (physicalConstraintSumSquares d s)) = 0 ↔ _
  rw [MvPolynomial.eval₂Hom_rename]
  change PhysicalPolynomial.eval (z ∘ ExactWitnessCoordinates.liftPhysicalCoordinates d s)
      (physicalConstraintSumSquares d s) = 0 ↔ _
  rw [physicalConstraintSumSquares_eval_eq_zero_iff,
    ExactWitnessCoordinates.physicalCoordinatesEquiv_symm_liftPhysicalCoordinates]

/-- Unit normalization of the independent environment witness. -/
def targetWitnessConstraintPolynomial (d : ℕ) (s : ForwardShape) :
    MvPolynomial (Fin (ExactWitnessCoordinates.coordinateCount d s)) ℤ :=
  unitResourceConstraint (ExactWitnessCoordinates.witnessCoordinates d s)

theorem targetWitnessConstraintPolynomial_eval_eq_zero_iff (d : ℕ) (s : ForwardShape)
    (z : Fin (ExactWitnessCoordinates.coordinateCount d s) → ℝ) :
    PhysicalPolynomial.eval z (targetWitnessConstraintPolynomial d s) = 0 ↔
      IsUnitVector ((ExactWitnessCoordinates.coordinatesEquiv d s).symm z).2.2.1 := by
  simp only [targetWitnessConstraintPolynomial, unitResourceConstraint_eval_eq_zero_iff,
    ExactWitnessCoordinates.coordinateVector_witnessCoordinates]

/-- Target coisometry, with the orientation `U Uᴴ = I`. -/
def targetCoisometryConstraintPolynomial (d : ℕ) (s : ForwardShape) :
    MvPolynomial (Fin (ExactWitnessCoordinates.coordinateCount d s)) ℤ :=
  ComplexPair.matrixEqualityConstraint
    (ComplexPair.matrixMultiply (targetPolynomial d s)
      (ComplexPair.matrixConjTranspose (targetPolynomial d s)))
    (ComplexPair.matrixIdentity (Fin d × Fin d))

theorem targetCoisometryConstraintPolynomial_eval_eq_zero_iff (d : ℕ) (s : ForwardShape)
    (z : Fin (ExactWitnessCoordinates.coordinateCount d s) → ℝ) :
    PhysicalPolynomial.eval z (targetCoisometryConstraintPolynomial d s) = 0 ↔
      ((ExactWitnessCoordinates.coordinatesEquiv d s).symm z).1 *
        ((ExactWitnessCoordinates.coordinatesEquiv d s).symm z).1ᴴ = 1 := by
  simp only [targetCoisometryConstraintPolynomial,
    ComplexPair.matrixEqualityConstraint_eval_eq_zero_iff,
    ComplexPair.evaluateMatrix_matrixMultiply, ComplexPair.evaluateMatrix_matrixConjTranspose,
    ComplexPair.evaluateMatrix_matrixIdentity, targetPolynomial_evaluate]

/-- Exact frozen dilation, with the actual global matrix on the left. -/
def targetFrozenConstraintPolynomial (d : ℕ) (s : ForwardShape) :
    MvPolynomial (Fin (ExactWitnessCoordinates.coordinateCount d s)) ℤ :=
  ComplexPair.matrixEqualityConstraint (globalPolynomial d s)
    (ComplexPair.matrixMultiply (witnessInsertPolynomial d s) (targetPolynomial d s))

theorem targetFrozenConstraintPolynomial_eval_eq_zero_iff (d : ℕ) (s : ForwardShape)
    (z : Fin (ExactWitnessCoordinates.coordinateCount d s) → ℝ) :
    PhysicalPolynomial.eval z (targetFrozenConstraintPolynomial d s) = 0 ↔
      globalIsometryRegrouped
        ((ExactWitnessCoordinates.coordinatesEquiv d s).symm z).2.1
        ((ExactWitnessCoordinates.coordinatesEquiv d s).symm z).2.2.2.1
        ((ExactWitnessCoordinates.coordinatesEquiv d s).symm z).2.2.2.2.1
        ((ExactWitnessCoordinates.coordinatesEquiv d s).symm z).2.2.2.2.2.1
        ((ExactWitnessCoordinates.coordinatesEquiv d s).symm z).2.2.2.2.2.2 =
          insertVector (Fin d × Fin d)
            ((ExactWitnessCoordinates.coordinatesEquiv d s).symm z).2.2.1 *
              ((ExactWitnessCoordinates.coordinatesEquiv d s).symm z).1 := by
  simp only [targetFrozenConstraintPolynomial,
    ComplexPair.matrixEqualityConstraint_eval_eq_zero_iff,
    ComplexPair.evaluateMatrix_matrixMultiply, globalPolynomial_evaluate,
    witnessInsertPolynomial_evaluate, targetPolynomial_evaluate]

/-- Four integer equations suffice for the entire seven-block witness locus. -/
def targetConstraintPolynomial (d : ℕ) (s : ForwardShape) :
    Fin 4 → MvPolynomial (Fin (ExactWitnessCoordinates.coordinateCount d s)) ℤ :=
  ![targetPhysicalConstraintPolynomial d s, targetWitnessConstraintPolynomial d s,
    targetCoisometryConstraintPolynomial d s, targetFrozenConstraintPolynomial d s]

theorem targetConstraintPolynomial_eval_eq_zero_iff (d : ℕ) (s : ForwardShape)
    (z : Fin (ExactWitnessCoordinates.coordinateCount d s) → ℝ) :
    (∀ i, PhysicalPolynomial.eval z (targetConstraintPolynomial d s i) = 0) ↔
      (ExactWitnessCoordinates.coordinatesEquiv d s).symm z ∈ targetExactWitnessSet d s := by
  simp only [targetConstraintPolynomial, Fin.forall_fin_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.forall_fin_zero, and_true]
  rw [targetPhysicalConstraintPolynomial_eval_eq_zero_iff,
    targetWitnessConstraintPolynomial_eval_eq_zero_iff,
    targetCoisometryConstraintPolynomial_eval_eq_zero_iff,
    targetFrozenConstraintPolynomial_eval_eq_zero_iff]
  rfl

/-- Normalized target purity as a rational polynomial on all seven raw blocks. -/
def targetPurityPolynomial (d : ℕ) (s : ForwardShape) :
    MvPolynomial (Fin (ExactWitnessCoordinates.coordinateCount d s)) ℚ :=
  MvPolynomial.C (((d : ℚ) ^ 4)⁻¹) *
    MvPolynomial.map (Int.castRingHom ℚ) (ComplexPair.purityNumerator (targetPolynomial d s))

/-- Exact evaluation, including dimension zero; no denominator depends on the variables. -/
theorem targetPurityPolynomial_evaluate (d : ℕ) (s : ForwardShape)
    (z : Fin (ExactWitnessCoordinates.coordinateCount d s) → ℝ) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) z (targetPurityPolynomial d s) =
      purity ((d : ℝ) ^ 4)⁻¹ ((ExactWitnessCoordinates.coordinatesEquiv d s).symm z).1 := by
  have hcast : (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ := by
    ext n
    simp
  have hc : algebraMap ℚ ℝ (((d : ℚ) ^ 4)⁻¹) = ((d : ℝ) ^ 4)⁻¹ := by simp
  rw [targetPurityPolynomial, map_mul, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_map_hom, hcast, hc]
  change ((d : ℝ) ^ 4)⁻¹ * PhysicalPolynomial.eval z
      (ComplexPair.purityNumerator (targetPolynomial d s)) = _
  rw [← ComplexPair.purity_evaluateMatrix, targetPolynomial_evaluate]

end NLQCLean.ExactWitnessPolynomial

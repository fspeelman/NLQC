import NLQCLean.Arithmetic.PhysicalScorePolynomial
import NLQCLean.Arithmetic.PhysicalPolynomialEncoding
import NLQCLean.Models.PVMPhysicalReachability
import NLQCLean.Models.ProjectiveScore

/-!
# Integer-polynomial encoding of the PVM score

For the PVM shape the decoders output a basis label in `Fin d × Fin d`. The five PVM blocks are
flattened into real coordinates; the unit-resource and isometry equations form one integer sum
of squares of degree four; and the joint correct-label score is

`d² · scorePVM M = Σ_i Σ_e |Σ_j F(((i, eA), (i, eB)), j) M(j, i)|²`,

an integer polynomial of degree twelve in the coordinates of `M` and of the blocks.
-/

namespace NLQCLean.PhysicalPolynomial

attribute [local implicit_reducible] Matrix

open Matrix MvPolynomial
open scoped Kronecker

noncomputable section

variable (d : ℕ) (s : Fin 8 → ℕ)

abbrev PVMDecoderAEntryIndex := ((Fin d × Fin d) × Fin (s 6)) × DecoderAInputIndex s
abbrev PVMDecoderBEntryIndex := ((Fin d × Fin d) × Fin (s 7)) × DecoderBInputIndex s

abbrev PVMComplexEntryIndex :=
  ResourceEntryIndex s ⊕ (EncoderAEntryIndex d s ⊕
    (EncoderBEntryIndex d s ⊕ (PVMDecoderAEntryIndex d s ⊕ PVMDecoderBEntryIndex d s)))

abbrev PVMCoordinateIndex := PVMComplexEntryIndex d s × Fin 2

def pvmComplexEntriesEquiv :
    PVMPhysicalBlocks d s ≃ₗ[ℝ] (PVMComplexEntryIndex d s → ℂ) where
  toFun x := Sum.elim x.1 (Sum.elim (fun q => x.2.1 q.1 q.2)
    (Sum.elim (fun q => x.2.2.1 q.1 q.2)
      (Sum.elim (fun q => x.2.2.2.1 q.1 q.2) (fun q => x.2.2.2.2 q.1 q.2))))
  invFun z := (fun q => z (Sum.inl q),
    Matrix.of (fun i j => z (Sum.inr (Sum.inl (i, j)))),
    Matrix.of (fun i j => z (Sum.inr (Sum.inr (Sum.inl (i, j))))),
    Matrix.of (fun i j => z (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j)))))),
    Matrix.of (fun i j => z (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, j)))))))
  left_inv _ := rfl
  right_inv z := by
    funext q
    rcases q with q | q | q | q | q <;> rfl
  map_add' x y := by
    funext q
    rcases q with q | q | q | q | q <;> rfl
  map_smul' c x := by
    funext q
    rcases q with q | q | q | q | q <;> rfl

noncomputable def pvmCoordinatesEquiv :
    PVMPhysicalBlocks d s ≃ₗ[ℝ] (PVMCoordinateIndex d s → ℝ) :=
  (pvmComplexEntriesEquiv d s).trans (complexRealCoordEquiv _)

def pvmResourceCoordinates : ResourceEntryIndex s × Fin 2 → PVMCoordinateIndex d s :=
  fun q => (Sum.inl q.1, q.2)

def pvmEncoderACoordinates : EncoderAEntryIndex d s × Fin 2 → PVMCoordinateIndex d s :=
  fun q => (Sum.inr (Sum.inl q.1), q.2)

def pvmEncoderBCoordinates : EncoderBEntryIndex d s × Fin 2 → PVMCoordinateIndex d s :=
  fun q => (Sum.inr (Sum.inr (Sum.inl q.1)), q.2)

def pvmDecoderACoordinates : PVMDecoderAEntryIndex d s × Fin 2 → PVMCoordinateIndex d s :=
  fun q => (Sum.inr (Sum.inr (Sum.inr (Sum.inl q.1))), q.2)

def pvmDecoderBCoordinates : PVMDecoderBEntryIndex d s × Fin 2 → PVMCoordinateIndex d s :=
  fun q => (Sum.inr (Sum.inr (Sum.inr (Sum.inr q.1))), q.2)

/-! ### Constraints -/

abbrev PVMConstraintIndex :=
  Unit ⊕ (((EncoderAInputIndex d s × EncoderAInputIndex d s) × Fin 2) ⊕
    (((EncoderBInputIndex d s × EncoderBInputIndex d s) × Fin 2) ⊕
      (((DecoderAInputIndex s × DecoderAInputIndex s) × Fin 2) ⊕
        ((DecoderBInputIndex s × DecoderBInputIndex s) × Fin 2))))

noncomputable def pvmConstraintPolynomial :
    PVMConstraintIndex d s → MvPolynomial (PVMCoordinateIndex d s) ℤ :=
  Sum.elim (fun _ => unitResourceConstraint (pvmResourceCoordinates d s))
    (Sum.elim (isometryPartConstraint (pvmEncoderACoordinates d s))
      (Sum.elim (isometryPartConstraint (pvmEncoderBCoordinates d s))
        (Sum.elim (isometryPartConstraint (pvmDecoderACoordinates d s))
          (isometryPartConstraint (pvmDecoderBCoordinates d s)))))

noncomputable def pvmConstraintSumSquares : MvPolynomial (PVMCoordinateIndex d s) ℤ :=
  constraintSumSquares (pvmConstraintPolynomial d s)

variable {d s}

theorem pvmConstraintSumSquares_eval_coordinates_eq_zero_iff (x : PVMPhysicalBlocks d s) :
    eval (pvmCoordinatesEquiv d s x) (pvmConstraintSumSquares d s) = 0 ↔
      x ∈ pvmPhysicalSet d s := by
  classical
  have hR : coordinateVector (pvmResourceCoordinates d s) (pvmCoordinatesEquiv d s x) = x.1 := by
    funext q
    apply Complex.ext <;> rfl
  have hA : coordinateMatrix (pvmEncoderACoordinates d s) (pvmCoordinatesEquiv d s x) = x.2.1 := by
    ext i j
    apply Complex.ext <;> rfl
  have hB : coordinateMatrix (pvmEncoderBCoordinates d s) (pvmCoordinatesEquiv d s x) =
      x.2.2.1 := by
    ext i j
    apply Complex.ext <;> rfl
  have hDA : coordinateMatrix (pvmDecoderACoordinates d s) (pvmCoordinatesEquiv d s x) =
      x.2.2.2.1 := by
    ext i j
    apply Complex.ext <;> rfl
  have hDB : coordinateMatrix (pvmDecoderBCoordinates d s) (pvmCoordinatesEquiv d s x) =
      x.2.2.2.2 := by
    ext i j
    apply Complex.ext <;> rfl
  rw [pvmConstraintSumSquares, constraintSumSquares_eval_eq_zero_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← hR]
      exact (unitResourceConstraint_eval_eq_zero_iff _ _).mp (h (Sum.inl ()))
    · rw [← hA]
      exact (isometryPartConstraints_eval_eq_zero_iff _ _).mp fun q => h (Sum.inr (Sum.inl q))
    · rw [← hB]
      exact (isometryPartConstraints_eval_eq_zero_iff _ _).mp
        fun q => h (Sum.inr (Sum.inr (Sum.inl q)))
    · rw [← hDA]
      exact (isometryPartConstraints_eval_eq_zero_iff _ _).mp
        fun q => h (Sum.inr (Sum.inr (Sum.inr (Sum.inl q))))
    · rw [← hDB]
      exact (isometryPartConstraints_eval_eq_zero_iff _ _).mp
        fun q => h (Sum.inr (Sum.inr (Sum.inr (Sum.inr q))))
  · rintro ⟨h0, h1, h2, h3, h4⟩ q
    rcases q with q | q | q | q | q
    · exact (unitResourceConstraint_eval_eq_zero_iff _ _).mpr (hR.symm ▸ h0)
    · exact (isometryPartConstraints_eval_eq_zero_iff _ _).mpr (hA.symm ▸ h1) q
    · exact (isometryPartConstraints_eval_eq_zero_iff _ _).mpr (hB.symm ▸ h2) q
    · exact (isometryPartConstraints_eval_eq_zero_iff _ _).mpr (hDA.symm ▸ h3) q
    · exact (isometryPartConstraints_eval_eq_zero_iff _ _).mpr (hDB.symm ▸ h4) q

/-! ### The score numerator -/

variable (d s)

abbrev PVMScoreCoordinateIndex :=
  ((LogicalIndex d × LogicalIndex d) × Fin 2) ⊕ PVMCoordinateIndex d s

def pvmTargetCoordinates :
    (LogicalIndex d × LogicalIndex d) × Fin 2 → PVMScoreCoordinateIndex d s := Sum.inl

def liftPVMCoordinates {ε : Type*} (entry : ε × Fin 2 → PVMCoordinateIndex d s) :
    ε × Fin 2 → PVMScoreCoordinateIndex d s := fun q => Sum.inr (entry q)

variable {d s}

def pvmScoreCoordinates (M : Matrix (LogicalIndex d) (LogicalIndex d) ℂ)
    (x : PVMPhysicalBlocks d s) : PVMScoreCoordinateIndex d s → ℝ :=
  Sum.elim (complexRealCoordEquiv (LogicalIndex d × LogicalIndex d) (fun q => M q.1 q.2))
    (pvmCoordinatesEquiv d s x)

variable (d s)

/-- The global amplitude, before output regrouping. -/
def pvmGlobalPolynomial :
    Matrix ((LogicalIndex d × Fin (s 6)) × (LogicalIndex d × Fin (s 7))) (LogicalIndex d)
      (ComplexPair (PVMScoreCoordinateIndex d s)) :=
  let VA := ComplexPair.matrixVariable (liftPVMCoordinates d s (pvmEncoderACoordinates d s))
  let VB := ComplexPair.matrixVariable (liftPVMCoordinates d s (pvmEncoderBCoordinates d s))
  let DA := ComplexPair.matrixVariable (liftPVMCoordinates d s (pvmDecoderACoordinates d s))
  let DB := ComplexPair.matrixVariable (liftPVMCoordinates d s (pvmDecoderBCoordinates d s))
  let J := ComplexPair.resourceInsert (ιA := Fin d) (ιB := Fin d)
    (liftPVMCoordinates d s (pvmResourceCoordinates d s))
  let encoded := ComplexPair.matrixMultiply (ComplexPair.matrixKronecker VA VB) J
  let exchanged := encoded.submatrix
    (exchangeEquiv (Fin (s 2)) (Fin (s 4)) (Fin (s 3)) (Fin (s 5))) id
  ComplexPair.matrixMultiply (ComplexPair.matrixKronecker DA DB) exchanged

theorem pvmGlobalPolynomial_degree_le :
    ∀ i j, ComplexPair.DegreeLE 5 (pvmGlobalPolynomial d s i j) := by
  have henc : ∀ i j, ComplexPair.DegreeLE 3 (ComplexPair.matrixMultiply
      (ComplexPair.matrixKronecker
        (ComplexPair.matrixVariable (liftPVMCoordinates d s (pvmEncoderACoordinates d s)))
        (ComplexPair.matrixVariable (liftPVMCoordinates d s (pvmEncoderBCoordinates d s))))
      (ComplexPair.resourceInsert (ιA := Fin d) (ιB := Fin d)
        (liftPVMCoordinates d s (pvmResourceCoordinates d s))) i j) :=
    ComplexPair.degree_matrixMultiply _ _
      (ComplexPair.degree_matrixKronecker _ _ (ComplexPair.degree_matrixVariable _)
        (ComplexPair.degree_matrixVariable _)) (ComplexPair.degree_resourceInsert _)
  have hdec : ∀ i j, ComplexPair.DegreeLE 2 (ComplexPair.matrixKronecker
      (ComplexPair.matrixVariable (liftPVMCoordinates d s (pvmDecoderACoordinates d s)))
      (ComplexPair.matrixVariable (liftPVMCoordinates d s (pvmDecoderBCoordinates d s))) i j) :=
    ComplexPair.degree_matrixKronecker _ _ (ComplexPair.degree_matrixVariable _)
      (ComplexPair.degree_matrixVariable _)
  exact ComplexPair.degree_matrixMultiply _ _ hdec
    (fun i j => henc (exchangeEquiv (Fin (s 2)) (Fin (s 4)) (Fin (s 3)) (Fin (s 5)) i) j)

variable {d s}

theorem pvmGlobalPolynomial_evaluate (M : Matrix (LogicalIndex d) (LogicalIndex d) ℂ)
    (x : PVMPhysicalBlocks d s) :
    ComplexPair.evaluateMatrix (pvmScoreCoordinates M x) (pvmGlobalPolynomial d s) =
      globalIsometry x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  simp only [pvmGlobalPolynomial, ComplexPair.evaluateMatrix_submatrix,
    ComplexPair.evaluateMatrix_matrixMultiply, ComplexPair.evaluateMatrix_matrixKronecker,
    ComplexPair.evaluateMatrix_matrixVariable, ComplexPair.evaluateMatrix_resourceInsert]
  change (x.2.2.2.1 ⊗ₖ x.2.2.2.2) *
    ((x.2.1 ⊗ₖ x.2.2.1) * insertResource (Fin d) (Fin d) x.1).submatrix
      (exchangeEquiv (Fin (s 2)) (Fin (s 4)) (Fin (s 3)) (Fin (s 5))) id = _
  rw [← exchangeMatrix_mul]
  rfl

variable (d s)

/-- The amplitude of the correct joint label `i` in environment slot `e`. -/
def pvmOverlapPolynomial (i : LogicalIndex d) (e : Fin (s 6) × Fin (s 7)) :
    ComplexPair (PVMScoreCoordinateIndex d s) :=
  ComplexPair.sum (fun j : LogicalIndex d =>
    ComplexPair.multiply (pvmGlobalPolynomial d s ((i, e.1), (i, e.2)) j)
      (ComplexPair.matrixVariable (pvmTargetCoordinates d s) j i))

/-- `d² × scorePVM`, as an integer polynomial. -/
def pvmScoreNumeratorPolynomial : MvPolynomial (PVMScoreCoordinateIndex d s) ℤ :=
  ∑ i : LogicalIndex d, ∑ e : Fin (s 6) × Fin (s 7),
    ComplexPair.normSquare (pvmOverlapPolynomial d s i e)

theorem pvmScoreNumeratorPolynomial_degree_le :
    (pvmScoreNumeratorPolynomial d s).totalDegree ≤ 12 := by
  apply totalDegree_finsetSum_le
  intro i _
  apply totalDegree_finsetSum_le
  intro e _
  exact ComplexPair.degree_normSquare (ComplexPair.degree_sum _ fun j =>
    ComplexPair.degree_multiply (pvmGlobalPolynomial_degree_le d s _ j)
      (ComplexPair.degree_matrixVariable _ j i))

variable {d s}

theorem pvmScoreNumeratorPolynomial_evaluate (M : Matrix (LogicalIndex d) (LogicalIndex d) ℂ)
    (x : PVMPhysicalBlocks d s) :
    eval (pvmScoreCoordinates M x) (pvmScoreNumeratorPolynomial d s) =
      ((d : ℝ) ^ 2) * pvmPhysicalScore M x := by
  have hcard : (Fintype.card (LogicalIndex d) : ℝ) = (d : ℝ) ^ 2 := by
    simp [LogicalIndex, sq]
  unfold pvmPhysicalScore
  rw [show operationalChannel x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 =
      channelOf ((globalIsometry x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).submatrix
        (outputRegroup (LogicalIndex d) (LogicalIndex d) (Fin (s 6)) (Fin (s 7))) id) from rfl,
    scorePVM_channelOf_regrouped, ← hcard, ← mul_assoc]
  by_cases hd : (Fintype.card (LogicalIndex d) : ℝ) = 0
  · have hempty : IsEmpty (LogicalIndex d) := by
      rw [← Fintype.card_eq_zero_iff]
      exact_mod_cast hd
    simp [pvmScoreNumeratorPolynomial]
  rw [mul_inv_cancel₀ hd, one_mul]
  simp only [pvmScoreNumeratorPolynomial, map_sum, ComplexPair.eval_normSquare]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun e _ => ?_
  congr 1
  simp only [pvmOverlapPolynomial, ComplexPair.evaluate_sum, ComplexPair.evaluate_multiply,
    Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hglobal := congrArg (fun A => A ((i, e.1), (i, e.2)) j) (pvmGlobalPolynomial_evaluate M x)
  simp only [ComplexPair.evaluateMatrix, Matrix.of_apply] at hglobal
  rw [hglobal]
  have htarget : ComplexPair.evaluate (pvmScoreCoordinates M x)
      (ComplexPair.matrixVariable (pvmTargetCoordinates d s) j i) = M j i := by
    dsimp only [ComplexPair.matrixVariable, Matrix.of_apply]
    rw [ComplexPair.evaluate_coordinatePair]
    rfl
  rw [htarget]
  rfl

end

end NLQCLean.PhysicalPolynomial

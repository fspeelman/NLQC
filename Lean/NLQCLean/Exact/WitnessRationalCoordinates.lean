import NLQCLean.Exact.ScalarCriticalValues
import NLQCLean.Arithmetic.PhysicalPolynomialEncoding

/-!
# Raw real coordinates for exact target witnesses

The target matrix, garbage vector and five physical blocks have one complex
coordinate per entry and two real coordinates per complex entry. Relabeling
the finite coordinate index by `Fin` introduces no rescaling or constraint.
The selectors reconstruct precisely the original seven blocks.
-/

noncomputable section

namespace NLQCLean.ExactWitnessCoordinates

attribute [local implicit_reducible] Matrix

open Matrix

abbrev LogicalIndex (d : ℕ) := Fin d × Fin d
abbrev WitnessEnvironmentIndex (s : ForwardShape) := Fin (s 6) × Fin (s 7)

/-- The target together with the original six-block exact witness. -/
abbrev Blocks (d : ℕ) (s : ForwardShape) :=
  Matrix (LogicalIndex d) (LogicalIndex d) ℂ × ShapeBlocks d s

/-- Target entries, garbage entries, then the five physical blocks. -/
abbrev ComplexEntryIndex (d : ℕ) (s : ForwardShape) :=
  (LogicalIndex d × LogicalIndex d) ⊕
    (WitnessEnvironmentIndex s ⊕ PhysicalPolynomial.PhysicalComplexEntryIndex d s)

/-- Exactly two raw real coordinates per complex entry. -/
abbrev RealCoordinateIndex (d : ℕ) (s : ForwardShape) :=
  ComplexEntryIndex d s × Fin 2

def coordinateCount (d : ℕ) (s : ForwardShape) : ℕ :=
  Fintype.card (RealCoordinateIndex d s)

/-- Forget the garbage block, retaining the original resource and four maps. -/
def physicalBlocks {d : ℕ} {s : ForwardShape} (x : ShapeBlocks d s) : PhysicalBlocks d s :=
  (x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2)

/-- Flatten all seven blocks without changing their entries. -/
def complexEntriesEquiv (d : ℕ) (s : ForwardShape) :
    Blocks d s ≃ₗ[ℝ] (ComplexEntryIndex d s → ℂ) where
  toFun y := Sum.elim (fun q => y.1 q.1 q.2)
    (Sum.elim y.2.2.1 (PhysicalPolynomial.physicalComplexEntriesEquiv d s
      (physicalBlocks y.2)))
  invFun z :=
    (Matrix.of (fun i j => z (Sum.inl (i, j))),
      (fun q => z (Sum.inr (Sum.inr (Sum.inl q))),
        fun q => z (Sum.inr (Sum.inl q)),
        Matrix.of (fun i j => z (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j)))))),
        Matrix.of (fun i j => z (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j))))))),
        Matrix.of (fun i j => z (Sum.inr (Sum.inr
          (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j)))))))),
        Matrix.of (fun i j => z (Sum.inr (Sum.inr
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, j))))))))))
  left_inv _ := rfl
  right_inv z := by
    funext q
    rcases q with q | q | q | q | q | q | q <;> rfl
  map_add' x y := by
    funext q
    rcases q with q | q | q | q | q | q | q <;> rfl
  map_smul' c x := by
    funext q
    rcases q with q | q | q | q | q | q | q <;> rfl

/-- Split each entry into its real and imaginary parts. -/
def rawCoordinatesEquiv (d : ℕ) (s : ForwardShape) :
    Blocks d s ≃ₗ[ℝ] (RealCoordinateIndex d s → ℝ) :=
  (complexEntriesEquiv d s).trans (complexRealCoordEquiv _)

/-- Relabel the finite raw coordinate index by its cardinality. -/
def indexEquiv (d : ℕ) (s : ForwardShape) :
    RealCoordinateIndex d s ≃ Fin (coordinateCount d s) :=
  Fintype.equivFin _

def coordinateRelabelEquiv (d : ℕ) (s : ForwardShape) :
    (RealCoordinateIndex d s → ℝ) ≃ₗ[ℝ] (Fin (coordinateCount d s) → ℝ) where
  toFun z := z ∘ (indexEquiv d s).symm
  invFun z := z ∘ indexEquiv d s
  left_inv z := by funext i; simp
  right_inv z := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The complete raw real coordinate equivalence on a `Fin` index. -/
def coordinatesEquiv (d : ℕ) (s : ForwardShape) :
    Blocks d s ≃ₗ[ℝ] (Fin (coordinateCount d s) → ℝ) :=
  (rawCoordinatesEquiv d s).trans (coordinateRelabelEquiv d s)

/-- Target-entry coordinates in the complete seven-block real index. -/
def targetCoordinates (d : ℕ) (s : ForwardShape) :
    (LogicalIndex d × LogicalIndex d) × Fin 2 → Fin (coordinateCount d s) :=
  fun q => indexEquiv d s (Sum.inl q.1, q.2)

/-- Garbage-vector coordinates in the complete seven-block real index. -/
def witnessCoordinates (d : ℕ) (s : ForwardShape) :
    WitnessEnvironmentIndex s × Fin 2 → Fin (coordinateCount d s) :=
  fun q => indexEquiv d s (Sum.inr (Sum.inl q.1), q.2)

/-- Include the existing five-block physical coordinates in the full index. -/
def liftPhysicalCoordinates (d : ℕ) (s : ForwardShape) :
    PhysicalPolynomial.PhysicalCoordinateIndex d s → Fin (coordinateCount d s) :=
  fun q => indexEquiv d s (Sum.inr (Sum.inr q.1), q.2)

def resourceCoordinates (d : ℕ) (s : ForwardShape) :
    PhysicalPolynomial.ResourceEntryIndex s × Fin 2 → Fin (coordinateCount d s) :=
  liftPhysicalCoordinates d s ∘ PhysicalPolynomial.resourceCoordinates d s

def encoderACoordinates (d : ℕ) (s : ForwardShape) :
    PhysicalPolynomial.EncoderAEntryIndex d s × Fin 2 → Fin (coordinateCount d s) :=
  liftPhysicalCoordinates d s ∘ PhysicalPolynomial.encoderACoordinates d s

def encoderBCoordinates (d : ℕ) (s : ForwardShape) :
    PhysicalPolynomial.EncoderBEntryIndex d s × Fin 2 → Fin (coordinateCount d s) :=
  liftPhysicalCoordinates d s ∘ PhysicalPolynomial.encoderBCoordinates d s

def decoderACoordinates (d : ℕ) (s : ForwardShape) :
    PhysicalPolynomial.DecoderAEntryIndex d s × Fin 2 → Fin (coordinateCount d s) :=
  liftPhysicalCoordinates d s ∘ PhysicalPolynomial.decoderACoordinates d s

def decoderBCoordinates (d : ℕ) (s : ForwardShape) :
    PhysicalPolynomial.DecoderBEntryIndex d s × Fin 2 → Fin (coordinateCount d s) :=
  liftPhysicalCoordinates d s ∘ PhysicalPolynomial.decoderBCoordinates d s

variable (d : ℕ) (s : ForwardShape)

@[simp] theorem coordinateMatrix_targetCoordinates (z : Fin (coordinateCount d s) → ℝ) :
    PhysicalPolynomial.coordinateMatrix (targetCoordinates d s) z =
      ((coordinatesEquiv d s).symm z).1 := rfl

@[simp] theorem coordinateVector_witnessCoordinates (z : Fin (coordinateCount d s) → ℝ) :
    PhysicalPolynomial.coordinateVector (witnessCoordinates d s) z =
      ((coordinatesEquiv d s).symm z).2.2.1 := rfl

@[simp] theorem coordinateVector_resourceCoordinates (z : Fin (coordinateCount d s) → ℝ) :
    PhysicalPolynomial.coordinateVector (resourceCoordinates d s) z =
      ((coordinatesEquiv d s).symm z).2.1 := rfl

@[simp] theorem coordinateMatrix_encoderACoordinates (z : Fin (coordinateCount d s) → ℝ) :
    PhysicalPolynomial.coordinateMatrix (encoderACoordinates d s) z =
      ((coordinatesEquiv d s).symm z).2.2.2.1 := rfl

@[simp] theorem coordinateMatrix_encoderBCoordinates (z : Fin (coordinateCount d s) → ℝ) :
    PhysicalPolynomial.coordinateMatrix (encoderBCoordinates d s) z =
      ((coordinatesEquiv d s).symm z).2.2.2.2.1 := rfl

@[simp] theorem coordinateMatrix_decoderACoordinates (z : Fin (coordinateCount d s) → ℝ) :
    PhysicalPolynomial.coordinateMatrix (decoderACoordinates d s) z =
      ((coordinatesEquiv d s).symm z).2.2.2.2.2.1 := rfl

@[simp] theorem coordinateMatrix_decoderBCoordinates (z : Fin (coordinateCount d s) → ℝ) :
    PhysicalPolynomial.coordinateMatrix (decoderBCoordinates d s) z =
      ((coordinatesEquiv d s).symm z).2.2.2.2.2.2 := rfl

/-- The existing physical coordinate equivalence agrees with the selectors. -/
theorem physicalCoordinatesEquiv_physicalBlocks (z : Fin (coordinateCount d s) → ℝ) :
    PhysicalPolynomial.physicalCoordinatesEquiv d s
        (physicalBlocks ((coordinatesEquiv d s).symm z).2) =
      z ∘ liftPhysicalCoordinates d s := by
  funext ⟨q, c⟩
  rcases q with q | q | q | q | q <;> fin_cases c <;> rfl

/-- Decoding the selected physical coordinates recovers the five physical blocks. -/
theorem physicalCoordinatesEquiv_symm_liftPhysicalCoordinates
    (z : Fin (coordinateCount d s) → ℝ) :
    (PhysicalPolynomial.physicalCoordinatesEquiv d s).symm
        (z ∘ liftPhysicalCoordinates d s) =
      physicalBlocks ((coordinatesEquiv d s).symm z).2 := by
  rw [← physicalCoordinatesEquiv_physicalBlocks d s z]
  exact (PhysicalPolynomial.physicalCoordinatesEquiv d s).symm_apply_apply _

/-- Encoding then decoding recovers the original target and witness tuple. -/
theorem coordinatesEquiv_symm_apply_apply (y : Blocks d s) :
    (coordinatesEquiv d s).symm (coordinatesEquiv d s y) = y :=
  (coordinatesEquiv d s).symm_apply_apply y

/-- Decoding then encoding recovers every raw real coordinate tuple. -/
theorem coordinatesEquiv_apply_symm_apply (z : Fin (coordinateCount d s) → ℝ) :
    coordinatesEquiv d s ((coordinatesEquiv d s).symm z) = z :=
  (coordinatesEquiv d s).apply_symm_apply z

@[simp] theorem coordinateMatrix_targetCoordinates_encode (y : Blocks d s) :
    PhysicalPolynomial.coordinateMatrix (targetCoordinates d s) (coordinatesEquiv d s y) = y.1 := by
  simp

@[simp] theorem coordinateVector_witnessCoordinates_encode (y : Blocks d s) :
    PhysicalPolynomial.coordinateVector (witnessCoordinates d s) (coordinatesEquiv d s y) =
      y.2.2.1 := by
  simp

@[simp] theorem coordinateVector_resourceCoordinates_encode (y : Blocks d s) :
    PhysicalPolynomial.coordinateVector (resourceCoordinates d s) (coordinatesEquiv d s y) =
      y.2.1 := by
  simp

@[simp] theorem coordinateMatrix_encoderACoordinates_encode (y : Blocks d s) :
    PhysicalPolynomial.coordinateMatrix (encoderACoordinates d s) (coordinatesEquiv d s y) =
      y.2.2.2.1 := by
  simp

@[simp] theorem coordinateMatrix_encoderBCoordinates_encode (y : Blocks d s) :
    PhysicalPolynomial.coordinateMatrix (encoderBCoordinates d s) (coordinatesEquiv d s y) =
      y.2.2.2.2.1 := by
  simp

@[simp] theorem coordinateMatrix_decoderACoordinates_encode (y : Blocks d s) :
    PhysicalPolynomial.coordinateMatrix (decoderACoordinates d s) (coordinatesEquiv d s y) =
      y.2.2.2.2.2.1 := by
  simp

@[simp] theorem coordinateMatrix_decoderBCoordinates_encode (y : Blocks d s) :
    PhysicalPolynomial.coordinateMatrix (decoderBCoordinates d s) (coordinatesEquiv d s y) =
      y.2.2.2.2.2.2 := by
  simp

end NLQCLean.ExactWitnessCoordinates

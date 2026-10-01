import NLQCLean.Arithmetic.PhysicalPolynomialConstraints

/-!
# Raw integer-polynomial encoding of the five physical blocks

An explicit real-linear equivalence splits every resource, encoder
and decoder entry into real and imaginary coordinates. The number of
coordinates is exactly the existing raw physical coordinate count. One
integer polynomial of degree at most four, formed by a sum of squares of
quadratic equations, vanishes exactly on the physical constraint set.
No rational score, coefficient-height, effective elimination or named-target
arithmetic certificate is supplied here.
-/

namespace NLQCLean.PhysicalPolynomial

attribute [local implicit_reducible] Matrix

open Matrix MvPolynomial

abbrev ResourceEntryIndex (s : Fin 8 → ℕ) := Fin (s 0) × Fin (s 1)
abbrev EncoderAInputIndex (d : ℕ) (s : Fin 8 → ℕ) := Fin d × Fin (s 0)
abbrev EncoderBInputIndex (d : ℕ) (s : Fin 8 → ℕ) := Fin d × Fin (s 1)
abbrev DecoderAInputIndex (s : Fin 8 → ℕ) := Fin (s 2) × Fin (s 5)
abbrev DecoderBInputIndex (s : Fin 8 → ℕ) := Fin (s 3) × Fin (s 4)
abbrev EncoderAEntryIndex (d : ℕ) (s : Fin 8 → ℕ) :=
  (Fin (s 2) × Fin (s 4)) × EncoderAInputIndex d s
abbrev EncoderBEntryIndex (d : ℕ) (s : Fin 8 → ℕ) :=
  (Fin (s 3) × Fin (s 5)) × EncoderBInputIndex d s
abbrev DecoderAEntryIndex (d : ℕ) (s : Fin 8 → ℕ) :=
  (Fin d × Fin (s 6)) × DecoderAInputIndex s
abbrev DecoderBEntryIndex (d : ℕ) (s : Fin 8 → ℕ) :=
  (Fin d × Fin (s 7)) × DecoderBInputIndex s

/-- The disjoint union of the entries of the five production blocks. -/
abbrev PhysicalComplexEntryIndex (d : ℕ) (s : Fin 8 → ℕ) :=
  ResourceEntryIndex s ⊕ (EncoderAEntryIndex d s ⊕
    (EncoderBEntryIndex d s ⊕ (DecoderAEntryIndex d s ⊕ DecoderBEntryIndex d s)))

/-- Exactly two real coordinates per entry, with no auxiliary witness. -/
abbrev PhysicalCoordinateIndex (d : ℕ) (s : Fin 8 → ℕ) :=
  PhysicalComplexEntryIndex d s × Fin 2

/-- Flatten the five-block tuple without changing any register. -/
def physicalComplexEntriesEquiv (d : ℕ) (s : Fin 8 → ℕ) :
    PhysicalBlocks d s ≃ₗ[ℝ] (PhysicalComplexEntryIndex d s → ℂ) where
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

/-- The raw real-coordinate equivalence. -/
noncomputable def physicalCoordinatesEquiv (d : ℕ) (s : Fin 8 → ℕ) :
    PhysicalBlocks d s ≃ₗ[ℝ] (PhysicalCoordinateIndex d s → ℝ) :=
  (physicalComplexEntriesEquiv d s).trans (complexRealCoordEquiv _)

/-- The coordinate index has precisely the established entry count. -/
theorem card_physicalCoordinateIndex (d : ℕ) (s : Fin 8 → ℕ) :
    Fintype.card (PhysicalCoordinateIndex d s) = physicalRawRealCoordinateCount d s := by
  simp only [PhysicalCoordinateIndex, PhysicalComplexEntryIndex, ResourceEntryIndex,
    EncoderAEntryIndex, EncoderBEntryIndex, DecoderAEntryIndex, DecoderBEntryIndex,
    EncoderAInputIndex, EncoderBInputIndex, DecoderAInputIndex, DecoderBInputIndex,
    Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, physicalRawRealCoordinateCount]
  ring

def resourceCoordinates (d : ℕ) (s : Fin 8 → ℕ) :
    ResourceEntryIndex s × Fin 2 → PhysicalCoordinateIndex d s :=
  fun q => (Sum.inl q.1, q.2)

def encoderACoordinates (d : ℕ) (s : Fin 8 → ℕ) :
    EncoderAEntryIndex d s × Fin 2 → PhysicalCoordinateIndex d s :=
  fun q => (Sum.inr (Sum.inl q.1), q.2)

def encoderBCoordinates (d : ℕ) (s : Fin 8 → ℕ) :
    EncoderBEntryIndex d s × Fin 2 → PhysicalCoordinateIndex d s :=
  fun q => (Sum.inr (Sum.inr (Sum.inl q.1)), q.2)

def decoderACoordinates (d : ℕ) (s : Fin 8 → ℕ) :
    DecoderAEntryIndex d s × Fin 2 → PhysicalCoordinateIndex d s :=
  fun q => (Sum.inr (Sum.inr (Sum.inr (Sum.inl q.1))), q.2)

def decoderBCoordinates (d : ℕ) (s : Fin 8 → ℕ) :
    DecoderBEntryIndex d s × Fin 2 → PhysicalCoordinateIndex d s :=
  fun q => (Sum.inr (Sum.inr (Sum.inr (Sum.inr q.1))), q.2)

/-- Both real and imaginary column-pair equations in one finite family. -/
noncomputable def isometryPartConstraint {σ m n : Type*} [Fintype m] [DecidableEq n]
    (entry : (m × n) × Fin 2 → σ) (q : (n × n) × Fin 2) : MvPolynomial σ ℤ :=
  if q.2 = 0 then isometryRealConstraint entry q.1.1 q.1.2
    else isometryImagConstraint entry q.1.1 q.1.2

theorem isometryPartConstraint_degree_le {σ m n : Type*} [Fintype m] [DecidableEq n]
    (entry : (m × n) × Fin 2 → σ) (q : (n × n) × Fin 2) :
    (isometryPartConstraint entry q).totalDegree ≤ 2 := by
  classical
  unfold isometryPartConstraint
  split
  · exact isometryRealConstraint_degree_le _ _ _
  · exact isometryImagConstraint_degree_le _ _ _

theorem isometryPartConstraints_eval_eq_zero_iff {σ m n : Type*}
    [Fintype m] [DecidableEq n]
    (entry : (m × n) × Fin 2 → σ) (x : σ → ℝ) :
    (∀ q, eval x (isometryPartConstraint entry q) = 0) ↔
      IsIsometry (coordinateMatrix entry x) := by
  classical
  rw [← isometryConstraints_eval_eq_zero_iff]
  constructor
  · intro h i j
    exact ⟨by simpa [isometryPartConstraint] using h ((i, j), 0),
      by simpa [isometryPartConstraint] using h ((i, j), 1)⟩
  · intro h ⟨⟨i, j⟩, c⟩
    fin_cases c
    · simpa [isometryPartConstraint] using (h i j).1
    · simpa [isometryPartConstraint] using (h i j).2

/-- One normalization equation and all four isometry equations. -/
abbrev PhysicalConstraintIndex (d : ℕ) (s : Fin 8 → ℕ) :=
  Unit ⊕ (((EncoderAInputIndex d s × EncoderAInputIndex d s) × Fin 2) ⊕
    (((EncoderBInputIndex d s × EncoderBInputIndex d s) × Fin 2) ⊕
      (((DecoderAInputIndex s × DecoderAInputIndex s) × Fin 2) ⊕
        ((DecoderBInputIndex s × DecoderBInputIndex s) × Fin 2))))

/-- An integer equation for every physical constraint. -/
noncomputable def physicalConstraintPolynomial (d : ℕ) (s : Fin 8 → ℕ) :
    PhysicalConstraintIndex d s → MvPolynomial (PhysicalCoordinateIndex d s) ℤ :=
  Sum.elim (fun _ => unitResourceConstraint (resourceCoordinates d s))
    (Sum.elim (isometryPartConstraint (encoderACoordinates d s))
      (Sum.elim (isometryPartConstraint (encoderBCoordinates d s))
        (Sum.elim (isometryPartConstraint (decoderACoordinates d s))
          (isometryPartConstraint (decoderBCoordinates d s)))))

theorem physicalConstraintPolynomial_degree_le (d : ℕ) (s : Fin 8 → ℕ)
    (q : PhysicalConstraintIndex d s) : (physicalConstraintPolynomial d s q).totalDegree ≤ 2 := by
  rcases q with q | q | q | q | q
  · exact unitResourceConstraint_degree_le _
  · exact isometryPartConstraint_degree_le _ _
  · exact isometryPartConstraint_degree_le _ _
  · exact isometryPartConstraint_degree_le _ _
  · exact isometryPartConstraint_degree_le _ _

/-- A single integer equation bundles precisely those physical constraints. -/
noncomputable def physicalConstraintSumSquares (d : ℕ) (s : Fin 8 → ℕ) :
    MvPolynomial (PhysicalCoordinateIndex d s) ℤ :=
  constraintSumSquares (physicalConstraintPolynomial d s)

theorem physicalConstraintSumSquares_degree_le (d : ℕ) (s : Fin 8 → ℕ) :
    (physicalConstraintSumSquares d s).totalDegree ≤ 4 :=
  constraintSumSquares_degree_le _ (physicalConstraintPolynomial_degree_le d s)

/-- Vanishing on arbitrary real coordinates is exactly membership of their
decoded five-block tuple in the production physical constraint set. -/
theorem physicalConstraintSumSquares_eval_eq_zero_iff (d : ℕ) (s : Fin 8 → ℕ)
    (x : PhysicalCoordinateIndex d s → ℝ) :
    eval x (physicalConstraintSumSquares d s) = 0 ↔
      (physicalCoordinatesEquiv d s).symm x ∈ physicalSet d s := by
  rw [physicalConstraintSumSquares, constraintSumSquares_eval_eq_zero_iff]
  change (∀ q, eval x (physicalConstraintPolynomial d s q) = 0) ↔
    IsUnitVector (coordinateVector (resourceCoordinates d s) x) ∧
    IsIsometry (coordinateMatrix (encoderACoordinates d s) x) ∧
    IsIsometry (coordinateMatrix (encoderBCoordinates d s) x) ∧
    IsIsometry (coordinateMatrix (decoderACoordinates d s) x) ∧
    IsIsometry (coordinateMatrix (decoderBCoordinates d s) x)
  constructor
  · intro h
    exact ⟨(unitResourceConstraint_eval_eq_zero_iff _ x).mp (h (Sum.inl ())),
      (isometryPartConstraints_eval_eq_zero_iff _ x).mp (fun q => h (Sum.inr (Sum.inl q))),
      (isometryPartConstraints_eval_eq_zero_iff _ x).mp
        (fun q => h (Sum.inr (Sum.inr (Sum.inl q)))),
      (isometryPartConstraints_eval_eq_zero_iff _ x).mp
        (fun q => h (Sum.inr (Sum.inr (Sum.inr (Sum.inl q))))),
      (isometryPartConstraints_eval_eq_zero_iff _ x).mp
        (fun q => h (Sum.inr (Sum.inr (Sum.inr (Sum.inr q)))))⟩
  · rintro ⟨hη, hVA, hVB, hDA, hDB⟩ q
    rcases q with q | q | q | q | q
    · exact (unitResourceConstraint_eval_eq_zero_iff _ x).mpr hη
    · exact (isometryPartConstraints_eval_eq_zero_iff _ x).mpr hVA q
    · exact (isometryPartConstraints_eval_eq_zero_iff _ x).mpr hVB q
    · exact (isometryPartConstraints_eval_eq_zero_iff _ x).mpr hDA q
    · exact (isometryPartConstraints_eval_eq_zero_iff _ x).mpr hDB q

/-- Encoding a point preserves and reflects the exact physical
constraints, including every empty-register shape. -/
theorem physicalConstraintSumSquares_eval_coordinates_eq_zero_iff
    (d : ℕ) (s : Fin 8 → ℕ) (x : PhysicalBlocks d s) :
    eval (physicalCoordinatesEquiv d s x) (physicalConstraintSumSquares d s) = 0 ↔
      x ∈ physicalSet d s := by
  rw [physicalConstraintSumSquares_eval_eq_zero_iff]
  simp only [LinearEquiv.symm_apply_apply]

end NLQCLean.PhysicalPolynomial

import NLQCLean.Arithmetic.ControlledPhaseLeastDeficit
import NLQCLean.Models.ClassicalCommunication.TranscriptCompression

/-!
# Integer-polynomial encoding of the transcript family

The transcript family of `eq:explicit-quantum-variables`, for two qubits. A shape is a
per-transcript block shape `s = (r, r, kA, kB, a, b, eA, eB)` and outcome counts `nA, nB`.
The parameters are a resource vector, branch maps `V_{A,x}`, `V_{B,y}` and decoders
`W_{A,xy}`, `W_{B,xy}`; for every transcript `(x, y)` they form a five-block tuple of the
charged model with shape `s`. The constraints are the unit resource, the two instrument
normalizations `Σ_x V_xᴴ V_x = I` and the decoder isometry equations, bundled into one integer
sum of squares of degree four. The score numerator is the sum over transcripts of the charged
phase-score numerator, renamed into the family coordinates; it has degree at most twelve and
`16 × score` as its value. Every feasible point is an actual finite free-classical protocol.
-/

namespace NLQCLean.TranscriptPolynomial

open Matrix MvPolynomial PhysicalPolynomial ClassicalCommunication

attribute [local implicit_reducible] Matrix

variable (s : Fin 8 → ℕ) (nA nB : ℕ)

/-! ### Coordinates -/

/-- Complex entries: the resource, every branch map and every conditional decoder. -/
abbrev TComplexEntryIndex :=
  ResourceEntryIndex s ⊕ ((Fin nA × EncoderAEntryIndex 2 s) ⊕ ((Fin nB × EncoderBEntryIndex 2 s) ⊕
    (((Fin nA × Fin nB) × DecoderAEntryIndex 2 s) ⊕ ((Fin nA × Fin nB) × DecoderBEntryIndex 2 s))))

/-- Two real coordinates per complex entry. -/
abbrev TCoordIndex := TComplexEntryIndex s nA nB × Fin 2

/-- The parameter blocks of the transcript family. -/
abbrev TBlocks :=
  (ResourceEntryIndex s → ℂ) ×
    (Fin nA → Matrix (Fin (s 2) × Fin (s 4)) (Fin 2 × Fin (s 0)) ℂ) ×
    (Fin nB → Matrix (Fin (s 3) × Fin (s 5)) (Fin 2 × Fin (s 1)) ℂ) ×
    (Fin nA → Fin nB → Matrix (Fin 2 × Fin (s 6)) (Fin (s 2) × Fin (s 5)) ℂ) ×
    (Fin nA → Fin nB → Matrix (Fin 2 × Fin (s 7)) (Fin (s 3) × Fin (s 4)) ℂ)

variable {s nA nB}

/-- The five-block tuple of one transcript. -/
def perTranscript (z : TBlocks s nA nB) (x : Fin nA) (y : Fin nB) : PhysicalBlocks 2 s :=
  (z.1, z.2.1 x, z.2.2.1 y, z.2.2.2.1 x y, z.2.2.2.2 x y)

variable (s nA nB)

/-- Flatten the parameter blocks. -/
def tEntriesEquiv : TBlocks s nA nB ≃ₗ[ℝ] (TComplexEntryIndex s nA nB → ℂ) where
  toFun z := Sum.elim z.1 (Sum.elim (fun q => z.2.1 q.1 q.2.1 q.2.2)
    (Sum.elim (fun q => z.2.2.1 q.1 q.2.1 q.2.2)
      (Sum.elim (fun q => z.2.2.2.1 q.1.1 q.1.2 q.2.1 q.2.2)
        (fun q => z.2.2.2.2 q.1.1 q.1.2 q.2.1 q.2.2))))
  invFun w := (fun q => w (Sum.inl q),
    fun x => Matrix.of fun i j => w (Sum.inr (Sum.inl (x, (i, j)))),
    fun y => Matrix.of fun i j => w (Sum.inr (Sum.inr (Sum.inl (y, (i, j))))),
    fun x y => Matrix.of fun i j => w (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((x, y), (i, j)))))),
    fun x y => Matrix.of fun i j => w (Sum.inr (Sum.inr (Sum.inr (Sum.inr ((x, y), (i, j)))))))
  left_inv _ := rfl
  right_inv w := by
    funext q
    rcases q with q | q | q | q | q <;> rfl
  map_add' z w := by
    funext q
    rcases q with q | q | q | q | q <;> rfl
  map_smul' c z := by
    funext q
    rcases q with q | q | q | q | q <;> rfl

/-- The raw real coordinates of the parameter blocks. -/
noncomputable def tCoordsEquiv : TBlocks s nA nB ≃ₗ[ℝ] (TCoordIndex s nA nB → ℝ) :=
  (tEntriesEquiv s nA nB).trans (complexRealCoordEquiv _)

/-- The coordinates of one transcript inside the family coordinates. -/
def transcriptRename (x : Fin nA) (y : Fin nB) :
    PhysicalCoordinateIndex 2 s → TCoordIndex s nA nB
  | (Sum.inl q, c) => (Sum.inl q, c)
  | (Sum.inr (Sum.inl q), c) => (Sum.inr (Sum.inl (x, q)), c)
  | (Sum.inr (Sum.inr (Sum.inl q)), c) => (Sum.inr (Sum.inr (Sum.inl (y, q))), c)
  | (Sum.inr (Sum.inr (Sum.inr (Sum.inl q))), c) =>
      (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((x, y), q)))), c)
  | (Sum.inr (Sum.inr (Sum.inr (Sum.inr q))), c) =>
      (Sum.inr (Sum.inr (Sum.inr (Sum.inr ((x, y), q)))), c)

variable {s nA nB}

theorem tCoords_comp_rename (z : TBlocks s nA nB) (x : Fin nA) (y : Fin nB) :
    tCoordsEquiv s nA nB z ∘ transcriptRename s nA nB x y =
      physicalCoordinatesEquiv 2 s (perTranscript z x y) := by
  funext ⟨q, c⟩
  rcases q with q | q | q | q | q <;> rfl

theorem card_tCoordIndex :
    Fintype.card (TCoordIndex s nA nB) =
      2 * (s 0 * s 1 + nA * (s 2 * s 4 * (2 * s 0)) + nB * (s 3 * s 5 * (2 * s 1)) +
        nA * nB * (2 * s 6 * (s 2 * s 5)) + nA * nB * (2 * s 7 * (s 3 * s 4))) := by
  simp only [TCoordIndex, TComplexEntryIndex, ResourceEntryIndex, EncoderAEntryIndex,
    EncoderBEntryIndex, DecoderAEntryIndex, DecoderBEntryIndex, EncoderAInputIndex,
    EncoderBInputIndex, DecoderAInputIndex, DecoderBInputIndex, Fintype.card_prod,
    Fintype.card_sum, Fintype.card_fin]
  ring

/-! ### The score numerator -/

variable (s nA nB)

/-- The sum over transcripts of the renamed charged phase-score numerators. -/
noncomputable def transcriptScorePolynomial : MvPolynomial (Fin 2 ⊕ TCoordIndex s nA nB) ℤ :=
  ∑ x, ∑ y, rename (Sum.map id (transcriptRename s nA nB x y))
    (controlledPhaseScoreNumeratorPolynomial s)

theorem transcriptScorePolynomial_degree_le :
    (transcriptScorePolynomial s nA nB).totalDegree ≤ 12 := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro x _
  apply MvPolynomial.totalDegree_finsetSum_le
  intro y _
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    (controlledPhaseScoreNumeratorPolynomial_degree_le s)

variable {s nA nB}

theorem transcriptScorePolynomial_evaluate (c t : ℝ) (z : TBlocks s nA nB) :
    PhysicalPolynomial.eval (Sum.elim ![c, t] (tCoordsEquiv s nA nB z))
        (transcriptScorePolynomial s nA nB) =
      ∑ x, ∑ y, 16 * physicalScore (qubitCornerPhase ⟨c, t⟩) (perTranscript z x y) := by
  simp only [transcriptScorePolynomial, map_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [← controlledPhaseScoreNumeratorPolynomial_evaluate]
  simp only [PhysicalPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_rename]
  congr 1
  funext u
  rcases u with u | u
  · rfl
  · change tCoordsEquiv s nA nB z (transcriptRename s nA nB x y u) =
      physicalCoordinatesEquiv 2 s (perTranscript z x y) u
    rw [← tCoords_comp_rename]
    rfl

/-! ### Instrument normalization -/

/-- Real part of `Σ_x V_xᴴ V_x - I`. -/
noncomputable def instrumentRealConstraint {σ ξ m n : Type*} [Fintype ξ] [Fintype m]
    [DecidableEq n] (entry : ξ → (m × n) × Fin 2 → σ) (i j : n) : MvPolynomial σ ℤ :=
  (∑ x, ∑ k, (X (entry x ((k, i), 0)) * X (entry x ((k, j), 0)) +
    X (entry x ((k, i), 1)) * X (entry x ((k, j), 1)))) - if i = j then 1 else 0

/-- Imaginary part of `Σ_x V_xᴴ V_x`. -/
noncomputable def instrumentImagConstraint {σ ξ m n : Type*} [Fintype ξ] [Fintype m]
    (entry : ξ → (m × n) × Fin 2 → σ) (i j : n) : MvPolynomial σ ℤ :=
  ∑ x, ∑ k, (X (entry x ((k, i), 0)) * X (entry x ((k, j), 1)) -
    X (entry x ((k, i), 1)) * X (entry x ((k, j), 0)))

theorem instrumentRealConstraint_eval {σ ξ m n : Type*} [Fintype ξ] [Fintype m] [DecidableEq n]
    (entry : ξ → (m × n) × Fin 2 → σ) (w : σ → ℝ) (i j : n) :
    PhysicalPolynomial.eval w (instrumentRealConstraint entry i j) =
      ((∑ x, (coordinateMatrix (entry x) w)ᴴ * coordinateMatrix (entry x) w) i j).re -
        ((1 : Matrix n n ℂ) i j).re := by
  classical
  by_cases h : i = j <;>
    simp [PhysicalPolynomial.eval, instrumentRealConstraint, coordinateMatrix, coordinateVector,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_re, Matrix.one_apply, h,
      Matrix.sum_apply]

theorem instrumentImagConstraint_eval {σ ξ m n : Type*} [Fintype ξ] [Fintype m]
    (entry : ξ → (m × n) × Fin 2 → σ) (w : σ → ℝ) (i j : n) :
    PhysicalPolynomial.eval w (instrumentImagConstraint entry i j) =
      ((∑ x, (coordinateMatrix (entry x) w)ᴴ * coordinateMatrix (entry x) w) i j).im := by
  classical
  simp [PhysicalPolynomial.eval, instrumentImagConstraint, coordinateMatrix, coordinateVector,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_im, sub_eq_add_neg,
    Matrix.sum_apply]

/-- Both parts in one finite family. -/
noncomputable def instrumentPartConstraint {σ ξ m n : Type*} [Fintype ξ] [Fintype m]
    [DecidableEq n] (entry : ξ → (m × n) × Fin 2 → σ) (q : (n × n) × Fin 2) :
    MvPolynomial σ ℤ :=
  if q.2 = 0 then instrumentRealConstraint entry q.1.1 q.1.2
    else instrumentImagConstraint entry q.1.1 q.1.2

theorem instrumentPartConstraints_eval_eq_zero_iff {σ ξ m n : Type*} [Fintype ξ] [Fintype m]
    [DecidableEq n] (entry : ξ → (m × n) × Fin 2 → σ) (w : σ → ℝ) :
    (∀ q, PhysicalPolynomial.eval w (instrumentPartConstraint entry q) = 0) ↔
      ∑ x, (coordinateMatrix (entry x) w)ᴴ * coordinateMatrix (entry x) w = 1 := by
  classical
  have h0 : ∀ i j : n, instrumentPartConstraint entry ((i, j), 0) =
      instrumentRealConstraint entry i j := fun i j => by
    rw [instrumentPartConstraint, ite_eq_left rfl]
  have h1 : ∀ i j : n, instrumentPartConstraint entry ((i, j), 1) =
      instrumentImagConstraint entry i j := fun i j => by
    rw [instrumentPartConstraint, ite_eq_right one_ne_zero]
  constructor
  · intro h
    apply Matrix.ext
    intro i j
    apply Complex.ext
    · have hr := h ((i, j), 0)
      rw [h0, instrumentRealConstraint_eval] at hr
      exact sub_eq_zero.mp hr
    · have hi := h ((i, j), 1)
      rw [h1, instrumentImagConstraint_eval] at hi
      by_cases hij : i = j <;> simpa [Matrix.one_apply, hij] using hi
  · intro h ⟨⟨i, j⟩, c⟩
    have hij := congrArg (fun V : Matrix n n ℂ => V i j) h
    obtain rfl | rfl : c = 0 ∨ c = 1 := by fin_cases c <;> simp
    · rw [h0, instrumentRealConstraint_eval]
      exact sub_eq_zero.mpr (congrArg Complex.re hij)
    · rw [h1, instrumentImagConstraint_eval]
      rw [hij]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem instrumentPartConstraint_degree_le {σ ξ m n : Type*} [Fintype ξ] [Fintype m]
    [DecidableEq n] (entry : ξ → (m × n) × Fin 2 → σ) (q : (n × n) × Fin 2) :
    (instrumentPartConstraint entry q).totalDegree ≤ 2 := by
  classical
  unfold instrumentPartConstraint instrumentRealConstraint instrumentImagConstraint
  split
  · apply (MvPolynomial.totalDegree_sub _ _).trans
    refine max_le ?_ ?_
    · refine MvPolynomial.totalDegree_finsetSum_le fun x _ =>
        MvPolynomial.totalDegree_finsetSum_le fun k _ => ?_
      exact (MvPolynomial.totalDegree_add _ _).trans
        (max_le (variableProduct_degree_le _ _) (variableProduct_degree_le _ _))
    · split <;> simp
  · refine MvPolynomial.totalDegree_finsetSum_le fun x _ =>
      MvPolynomial.totalDegree_finsetSum_le fun k _ => ?_
    exact (MvPolynomial.totalDegree_sub _ _).trans
      (max_le (variableProduct_degree_le _ _) (variableProduct_degree_le _ _))

/-! ### The family constraints -/

variable (s nA nB)

def entryA (x : Fin nA) : EncoderAEntryIndex 2 s × Fin 2 → TCoordIndex s nA nB :=
  fun q => (Sum.inr (Sum.inl (x, q.1)), q.2)

def entryB (y : Fin nB) : EncoderBEntryIndex 2 s × Fin 2 → TCoordIndex s nA nB :=
  fun q => (Sum.inr (Sum.inr (Sum.inl (y, q.1))), q.2)

def entryDA (x : Fin nA) (y : Fin nB) : DecoderAEntryIndex 2 s × Fin 2 → TCoordIndex s nA nB :=
  fun q => (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((x, y), q.1)))), q.2)

def entryDB (x : Fin nA) (y : Fin nB) : DecoderBEntryIndex 2 s × Fin 2 → TCoordIndex s nA nB :=
  fun q => (Sum.inr (Sum.inr (Sum.inr (Sum.inr ((x, y), q.1)))), q.2)

def entryR : ResourceEntryIndex s × Fin 2 → TCoordIndex s nA nB := fun q => (Sum.inl q.1, q.2)

/-- The unit resource, two instrument normalizations and all decoder isometry equations. -/
abbrev TConstraintIndex :=
  Unit ⊕ (((EncoderAInputIndex 2 s × EncoderAInputIndex 2 s) × Fin 2) ⊕
    (((EncoderBInputIndex 2 s × EncoderBInputIndex 2 s) × Fin 2) ⊕
      (((Fin nA × Fin nB) × ((DecoderAInputIndex s × DecoderAInputIndex s) × Fin 2)) ⊕
        ((Fin nA × Fin nB) × ((DecoderBInputIndex s × DecoderBInputIndex s) × Fin 2)))))

noncomputable def transcriptConstraintPolynomial :
    TConstraintIndex s nA nB → MvPolynomial (TCoordIndex s nA nB) ℤ :=
  Sum.elim (fun _ => unitResourceConstraint (entryR s nA nB))
    (Sum.elim (instrumentPartConstraint (entryA s nA nB))
      (Sum.elim (instrumentPartConstraint (entryB s nA nB))
        (Sum.elim (fun p => isometryPartConstraint (entryDA s nA nB p.1.1 p.1.2) p.2)
          (fun p => isometryPartConstraint (entryDB s nA nB p.1.1 p.1.2) p.2))))

/-- One integer sum of squares for all transcript constraints. -/
noncomputable def transcriptConstraintSumSquares : MvPolynomial (TCoordIndex s nA nB) ℤ :=
  constraintSumSquares (transcriptConstraintPolynomial s nA nB)

theorem transcriptConstraintSumSquares_degree_le :
    (transcriptConstraintSumSquares s nA nB).totalDegree ≤ 4 := by
  apply constraintSumSquares_degree_le
  intro q
  rcases q with q | q | q | q | q
  · exact unitResourceConstraint_degree_le _
  · exact instrumentPartConstraint_degree_le _ _
  · exact instrumentPartConstraint_degree_le _ _
  · exact isometryPartConstraint_degree_le _ _
  · exact isometryPartConstraint_degree_le _ _

/-- The physical points of the transcript family. -/
def transcriptSet : Set (TBlocks s nA nB) :=
  {z | IsUnitVector z.1 ∧ (∑ x, (z.2.1 x)ᴴ * z.2.1 x = 1) ∧ (∑ y, (z.2.2.1 y)ᴴ * z.2.2.1 y = 1) ∧
    (∀ x y, IsIsometry (z.2.2.2.1 x y)) ∧ ∀ x y, IsIsometry (z.2.2.2.2 x y)}

variable {s nA nB}

theorem coordinateVector_entryR (z : TBlocks s nA nB) :
    coordinateVector (entryR s nA nB) (tCoordsEquiv s nA nB z) = z.1 := by
  funext q
  apply Complex.ext <;> rfl

theorem coordinateMatrix_entryA (z : TBlocks s nA nB) (x : Fin nA) :
    coordinateMatrix (entryA s nA nB x) (tCoordsEquiv s nA nB z) = z.2.1 x := by
  ext i j
  apply Complex.ext <;> rfl

theorem coordinateMatrix_entryB (z : TBlocks s nA nB) (y : Fin nB) :
    coordinateMatrix (entryB s nA nB y) (tCoordsEquiv s nA nB z) = z.2.2.1 y := by
  ext i j
  apply Complex.ext <;> rfl

theorem coordinateMatrix_entryDA (z : TBlocks s nA nB) (x : Fin nA) (y : Fin nB) :
    coordinateMatrix (entryDA s nA nB x y) (tCoordsEquiv s nA nB z) = z.2.2.2.1 x y := by
  ext i j
  apply Complex.ext <;> rfl

theorem coordinateMatrix_entryDB (z : TBlocks s nA nB) (x : Fin nA) (y : Fin nB) :
    coordinateMatrix (entryDB s nA nB x y) (tCoordsEquiv s nA nB z) = z.2.2.2.2 x y := by
  ext i j
  apply Complex.ext <;> rfl

theorem transcriptConstraintSumSquares_eval_eq_zero_iff (z : TBlocks s nA nB) :
    PhysicalPolynomial.eval (tCoordsEquiv s nA nB z) (transcriptConstraintSumSquares s nA nB) = 0 ↔
      z ∈ transcriptSet s nA nB := by
  classical
  rw [transcriptConstraintSumSquares, constraintSumSquares_eval_eq_zero_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← coordinateVector_entryR z]
      exact (unitResourceConstraint_eval_eq_zero_iff _ _).mp (h (Sum.inl ()))
    · simpa only [coordinateMatrix_entryA] using
        (instrumentPartConstraints_eval_eq_zero_iff (entryA s nA nB) _).mp
          fun q => h (Sum.inr (Sum.inl q))
    · simpa only [coordinateMatrix_entryB] using
        (instrumentPartConstraints_eval_eq_zero_iff (entryB s nA nB) _).mp
          fun q => h (Sum.inr (Sum.inr (Sum.inl q)))
    · intro x y
      rw [← coordinateMatrix_entryDA z x y]
      exact (isometryPartConstraints_eval_eq_zero_iff _ _).mp
        fun q => h (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((x, y), q)))))
    · intro x y
      rw [← coordinateMatrix_entryDB z x y]
      exact (isometryPartConstraints_eval_eq_zero_iff _ _).mp
        fun q => h (Sum.inr (Sum.inr (Sum.inr (Sum.inr ((x, y), q)))))
  · rintro ⟨hR, hA, hB, hDA, hDB⟩ q
    rcases q with q | q | q | ⟨⟨x, y⟩, q⟩ | ⟨⟨x, y⟩, q⟩
    · exact (unitResourceConstraint_eval_eq_zero_iff _ _).mpr ((coordinateVector_entryR z).symm ▸ hR)
    · exact (instrumentPartConstraints_eval_eq_zero_iff (entryA s nA nB) _).mpr
        (by simpa only [coordinateMatrix_entryA] using hA) q
    · exact (instrumentPartConstraints_eval_eq_zero_iff (entryB s nA nB) _).mpr
        (by simpa only [coordinateMatrix_entryB] using hB) q
    · exact (isometryPartConstraints_eval_eq_zero_iff _ _).mpr
        ((coordinateMatrix_entryDA z x y).symm ▸ hDA x y) q
    · exact (isometryPartConstraints_eval_eq_zero_iff _ _).mpr
        ((coordinateMatrix_entryDB z x y).symm ▸ hDB x y) q

/-! ### Physical protocols -/

/-- A physical point of the family is an actual finite free-classical protocol. -/
def toProtocol (z : TBlocks s nA nB) (hz : z ∈ transcriptSet s nA nB) :
    FiniteClassicalProtocol (Fin 2) (Fin 2) (Fin (s 0)) (Fin (s 1)) (Fin (s 2)) (Fin (s 3))
      (Fin (s 4)) (Fin (s 5)) (Fin nA) (Fin nB) Unit Unit (Fin 2) (Fin 2) (Fin (s 6)) (Fin (s 7)) where
  resource := z.1
  resource_unit := hz.1
  instrumentA := ⟨fun x _ => z.2.1 x, by simpa only [Fintype.sum_unique] using hz.2.1⟩
  instrumentB := ⟨fun y _ => z.2.2.1 y, by simpa only [Fintype.sum_unique] using hz.2.2.1⟩
  decA := z.2.2.2.1
  decB := z.2.2.2.2
  decA_isometry := hz.2.2.2.1
  decB_isometry := hz.2.2.2.2

/-- The blocks of a single-operator protocol of the family shape. -/
def ofProtocol (Q : FiniteClassicalProtocol (Fin 2) (Fin 2) (Fin (s 0)) (Fin (s 1)) (Fin (s 2))
    (Fin (s 3)) (Fin (s 4)) (Fin (s 5)) (Fin nA) (Fin nB) Unit Unit (Fin 2) (Fin 2) (Fin (s 6))
    (Fin (s 7))) : TBlocks s nA nB :=
  (Q.resource, fun x => Q.instrumentA.operator x (), fun y => Q.instrumentB.operator y (),
    Q.decA, Q.decB)

theorem ofProtocol_mem (Q : FiniteClassicalProtocol (Fin 2) (Fin 2) (Fin (s 0)) (Fin (s 1))
    (Fin (s 2)) (Fin (s 3)) (Fin (s 4)) (Fin (s 5)) (Fin nA) (Fin nB) Unit Unit (Fin 2) (Fin 2)
    (Fin (s 6)) (Fin (s 7))) : ofProtocol Q ∈ transcriptSet s nA nB := by
  refine ⟨Q.resource_unit, ?_, ?_, Q.decA_isometry, Q.decB_isometry⟩
  · exact (by simpa only [Fintype.sum_unique] using Q.instrumentA.normalized :
      ∑ x, (Q.instrumentA.operator x default)ᴴ * Q.instrumentA.operator x default = 1)
  · exact (by simpa only [Fintype.sum_unique] using Q.instrumentB.normalized :
      ∑ y, (Q.instrumentB.operator y default)ᴴ * Q.instrumentB.operator y default = 1)

theorem toProtocol_ofProtocol (Q : FiniteClassicalProtocol (Fin 2) (Fin 2) (Fin (s 0))
    (Fin (s 1)) (Fin (s 2)) (Fin (s 3)) (Fin (s 4)) (Fin (s 5)) (Fin nA) (Fin nB) Unit Unit
    (Fin 2) (Fin 2) (Fin (s 6)) (Fin (s 7))) :
    (toProtocol (ofProtocol Q) (ofProtocol_mem Q)).operationalChannel = Q.operationalChannel :=
  rfl

/-- The score of a physical point is the sum of the per-transcript charged scores. -/
theorem scoreU_toProtocol (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (z : TBlocks s nA nB)
    (hz : z ∈ transcriptSet s nA nB) :
    scoreU U (toProtocol z hz).operationalChannel =
      ∑ x, ∑ y, physicalScore U (perTranscript z x y) := by
  have h := map_sum (unitaryScoreRealLinear U) (fun x => ∑ y, ∑ u : Unit, ∑ v : Unit,
    channelOf (((toProtocol z hz).branchAmplitude x y u v).submatrix
      (outputRegroup (Fin 2) (Fin 2) (Fin (s 6)) (Fin (s 7))) id)) Finset.univ
  change scoreU U (∑ x, ∑ y, ∑ u : Unit, ∑ v : Unit, _) = _
  refine h.trans (Finset.sum_congr rfl fun x _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Fintype.sum_unique]
  rfl

end NLQCLean.TranscriptPolynomial

import NLQCLean.Arithmetic.PhysicalPolynomialEncoding

/-!
# Integer polynomials for raw physical target scores

Real and imaginary coordinates of both the target and the five physical
blocks are variables. The normalized score has an integer-polynomial
numerator after clearing the square of the logical input dimension.
No coefficient-height, elimination or named-target arithmetic conclusion is
claimed.
-/

noncomputable section

namespace NLQCLean.PhysicalPolynomial

attribute [local implicit_reducible] Matrix

open Matrix MvPolynomial
open scoped BigOperators Kronecker

/-- A complex expression represented by two integer polynomials. -/
abbrev ComplexPair (σ : Type*) := MvPolynomial σ ℤ × MvPolynomial σ ℤ

namespace ComplexPair

variable {σ : Type*}

noncomputable def evaluate (x : σ → ℝ) (p : ComplexPair σ) : ℂ :=
  ⟨eval x p.1, eval x p.2⟩

def coordinatePair (re im : σ) : ComplexPair σ := (X re, X im)

def multiply (p q : ComplexPair σ) : ComplexPair σ :=
  (p.1 * q.1 - p.2 * q.2, p.1 * q.2 + p.2 * q.1)

def conjugate (p : ComplexPair σ) : ComplexPair σ := (p.1, -p.2)

noncomputable def sum {ε : Type*} [Fintype ε] (p : ε → ComplexPair σ) : ComplexPair σ :=
  (∑ e, (p e).1, ∑ e, (p e).2)

def normSquare (p : ComplexPair σ) : MvPolynomial σ ℤ := p.1 ^ 2 + p.2 ^ 2

@[simp] theorem evaluate_zero (x : σ → ℝ) : evaluate x (0, 0) = 0 := by
  apply Complex.ext <;> simp [evaluate]

@[simp] theorem evaluate_coordinatePair (x : σ → ℝ) (re im : σ) :
    evaluate x (coordinatePair re im) = ⟨x re, x im⟩ := by
  apply Complex.ext <;> simp [evaluate, coordinatePair, eval]

@[simp] theorem evaluate_multiply (x : σ → ℝ) (p q : ComplexPair σ) :
    evaluate x (multiply p q) = evaluate x p * evaluate x q := by
  apply Complex.ext <;> simp [evaluate, multiply, Complex.mul_re, Complex.mul_im]

@[simp] theorem evaluate_conjugate (x : σ → ℝ) (p : ComplexPair σ) :
    evaluate x (conjugate p) = star (evaluate x p) := by
  apply Complex.ext <;> simp [evaluate, conjugate]

@[simp] theorem evaluate_sum {ε : Type*} [Fintype ε]
    (x : σ → ℝ) (p : ε → ComplexPair σ) :
    evaluate x (sum p) = ∑ e, evaluate x (p e) := by
  apply Complex.ext <;> simp [evaluate, sum, Complex.re_sum, Complex.im_sum]

@[simp] theorem eval_normSquare (x : σ → ℝ) (p : ComplexPair σ) :
    eval x (normSquare p) = Complex.normSq (evaluate x p) := by
  simp [evaluate, normSquare, Complex.normSq_apply, pow_two]

def DegreeLE (D : ℕ) (p : ComplexPair σ) : Prop :=
  p.1.totalDegree ≤ D ∧ p.2.totalDegree ≤ D

theorem degree_coordinatePair (re im : σ) : DegreeLE 1 (coordinatePair re im) := by
  simp [DegreeLE, coordinatePair]

theorem degree_zero (D : ℕ) : DegreeLE D ((0, 0) : ComplexPair σ) := by
  simp [DegreeLE]

theorem degree_multiply {D E : ℕ} {p q : ComplexPair σ}
    (hp : DegreeLE D p) (hq : DegreeLE E q) : DegreeLE (D + E) (multiply p q) := by
  have h11 := (totalDegree_mul p.1 q.1).trans (Nat.add_le_add hp.1 hq.1)
  have h22 := (totalDegree_mul p.2 q.2).trans (Nat.add_le_add hp.2 hq.2)
  have h12 := (totalDegree_mul p.1 q.2).trans (Nat.add_le_add hp.1 hq.2)
  have h21 := (totalDegree_mul p.2 q.1).trans (Nat.add_le_add hp.2 hq.1)
  exact ⟨(totalDegree_sub _ _).trans (max_le h11 h22),
    (totalDegree_add _ _).trans (max_le h12 h21)⟩

theorem degree_conjugate {D : ℕ} {p : ComplexPair σ} (hp : DegreeLE D p) :
    DegreeLE D (conjugate p) := by
  simpa only [DegreeLE, conjugate, totalDegree_neg] using hp

theorem degree_sum {D : ℕ} {ε : Type*} [Fintype ε]
    (p : ε → ComplexPair σ) (hp : ∀ e, DegreeLE D (p e)) : DegreeLE D (sum p) :=
  ⟨totalDegree_finsetSum_le (fun e _ => (hp e).1),
    totalDegree_finsetSum_le (fun e _ => (hp e).2)⟩

theorem degree_normSquare {D : ℕ} {p : ComplexPair σ} (hp : DegreeLE D p) :
    (normSquare p).totalDegree ≤ 2 * D := by
  apply (totalDegree_add _ _).trans
  exact max_le ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 hp.1))
    ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 hp.2))

/-- Matrix multiplication assembled only from integer polynomial operations. -/
noncomputable def matrixMultiply {m n k : Type*} [Fintype n]
    (P : Matrix m n (ComplexPair σ)) (Q : Matrix n k (ComplexPair σ)) :
    Matrix m k (ComplexPair σ) := Matrix.of fun i j => sum (fun q => multiply (P i q) (Q q j))

def matrixKronecker {m n k l : Type*}
    (P : Matrix m n (ComplexPair σ)) (Q : Matrix k l (ComplexPair σ)) :
    Matrix (m × k) (n × l) (ComplexPair σ) :=
  Matrix.of fun i j => multiply (P i.1 j.1) (Q i.2 j.2)

def matrixVariable {m n : Type*} (entry : (m × n) × Fin 2 → σ) :
    Matrix m n (ComplexPair σ) :=
  Matrix.of fun i j => coordinatePair (entry ((i, j), 0)) (entry ((i, j), 1))

noncomputable def evaluateMatrix {m n : Type*} (x : σ → ℝ)
    (P : Matrix m n (ComplexPair σ)) : Matrix m n ℂ :=
  Matrix.of fun i j => evaluate x (P i j)

@[simp] theorem evaluateMatrix_matrixVariable {m n : Type*}
    (x : σ → ℝ) (entry : (m × n) × Fin 2 → σ) :
    evaluateMatrix x (matrixVariable entry) = coordinateMatrix entry x := by
  ext i j
  exact evaluate_coordinatePair x _ _

@[simp] theorem evaluateMatrix_matrixMultiply {m n k : Type*} [Fintype n]
    (x : σ → ℝ) (P : Matrix m n (ComplexPair σ)) (Q : Matrix n k (ComplexPair σ)) :
    evaluateMatrix x (matrixMultiply P Q) = evaluateMatrix x P * evaluateMatrix x Q := by
  ext i j
  simp only [evaluateMatrix, matrixMultiply, Matrix.of_apply, evaluate_sum,
    evaluate_multiply, Matrix.mul_apply]

@[simp] theorem evaluateMatrix_matrixKronecker {m n k l : Type*}
    (x : σ → ℝ) (P : Matrix m n (ComplexPair σ)) (Q : Matrix k l (ComplexPair σ)) :
    evaluateMatrix x (matrixKronecker P Q) = evaluateMatrix x P ⊗ₖ evaluateMatrix x Q := by
  ext i j
  exact evaluate_multiply x _ _

theorem degree_matrixMultiply {m n k : Type*} [Fintype n] {D E : ℕ}
    (P : Matrix m n (ComplexPair σ)) (Q : Matrix n k (ComplexPair σ))
    (hP : ∀ i j, DegreeLE D (P i j)) (hQ : ∀ i j, DegreeLE E (Q i j)) :
    ∀ i j, DegreeLE (D + E) (matrixMultiply P Q i j) :=
  fun i j => degree_sum _ (fun q => degree_multiply (hP i q) (hQ q j))

theorem degree_matrixKronecker {m n k l : Type*} {D E : ℕ}
    (P : Matrix m n (ComplexPair σ)) (Q : Matrix k l (ComplexPair σ))
    (hP : ∀ i j, DegreeLE D (P i j)) (hQ : ∀ i j, DegreeLE E (Q i j)) :
    ∀ i j, DegreeLE (D + E) (matrixKronecker P Q i j) :=
  fun i j => degree_multiply (hP i.1 j.1) (hQ i.2 j.2)

theorem degree_matrixVariable {m n : Type*} (entry : (m × n) × Fin 2 → σ) :
    ∀ i j, DegreeLE 1 (matrixVariable entry i j) := fun _ _ => degree_coordinatePair _ _

end ComplexPair

namespace ComplexPair

/-- The resource insertion, represented without any noninteger scalar. -/
def resourceInsert {σ ιA ιB ρA ρB : Type*} [DecidableEq ιA] [DecidableEq ιB]
    (entry : (ρA × ρB) × Fin 2 → σ) :
    Matrix ((ιA × ρA) × (ιB × ρB)) (ιA × ιB) (ComplexPair σ) :=
  Matrix.of fun p q => if p.1.1 = q.1 ∧ p.2.1 = q.2 then
    coordinatePair (entry ((p.1.2, p.2.2), 0)) (entry ((p.1.2, p.2.2), 1)) else (0, 0)

@[simp] theorem evaluateMatrix_resourceInsert {σ ιA ιB ρA ρB : Type*}
    [DecidableEq ιA] [DecidableEq ιB]
    (x : σ → ℝ) (entry : (ρA × ρB) × Fin 2 → σ) :
    evaluateMatrix x (resourceInsert (ιA := ιA) (ιB := ιB) entry) =
      insertResource ιA ιB (coordinateVector entry x) := by
  ext p q
  rw [insertResource_apply_ite]
  by_cases h : p.1.1 = q.1 ∧ p.2.1 = q.2 <;>
    simp [evaluateMatrix, resourceInsert, h, coordinateVector]

theorem degree_resourceInsert {σ ιA ιB ρA ρB : Type*}
    [DecidableEq ιA] [DecidableEq ιB]
    (entry : (ρA × ρB) × Fin 2 → σ) :
    ∀ i j, DegreeLE 1 (resourceInsert (ιA := ιA) (ιB := ιB) entry i j) := by
  intro i j
  dsimp only [resourceInsert, Matrix.of_apply]
  split
  · exact degree_coordinatePair _ _
  · exact degree_zero _

@[simp] theorem evaluateMatrix_submatrix {σ m n m' n' : Type*}
    (x : σ → ℝ) (P : Matrix m n (ComplexPair σ)) (f : m' → m) (g : n' → n) :
    evaluateMatrix x (P.submatrix f g) = (evaluateMatrix x P).submatrix f g := rfl

end ComplexPair

abbrev LogicalIndex (d : ℕ) := Fin d × Fin d
abbrev PhysicalEnvironmentIndex (s : Fin 8 → ℕ) := Fin (s 6) × Fin (s 7)

/-- Target parameters are separate from the physical coordinates. -/
abbrev PhysicalScoreCoordinateIndex (d : ℕ) (s : Fin 8 → ℕ) :=
  ((LogicalIndex d × LogicalIndex d) × Fin 2) ⊕ PhysicalCoordinateIndex d s

def targetScoreCoordinates (d : ℕ) (s : Fin 8 → ℕ) :
    (LogicalIndex d × LogicalIndex d) × Fin 2 → PhysicalScoreCoordinateIndex d s := Sum.inl

def liftPhysicalScoreCoordinates {d : ℕ} {s : Fin 8 → ℕ} {ε : Type*}
    (entry : ε × Fin 2 → PhysicalCoordinateIndex d s) :
    ε × Fin 2 → PhysicalScoreCoordinateIndex d s := fun q => Sum.inr (entry q)

/-- The full score-coordinate count includes exactly two coordinates per
target entry; these are not part of the raw physical entry count. -/
theorem card_physicalScoreCoordinateIndex (d : ℕ) (s : Fin 8 → ℕ) :
    Fintype.card (PhysicalScoreCoordinateIndex d s) =
      physicalRawRealCoordinateCount d s + 2 * d ^ 4 := by
  rw [Fintype.card_sum, card_physicalCoordinateIndex]
  simp only [LogicalIndex, Fintype.card_prod, Fintype.card_fin]
  ring

/-- Encode an arbitrary target and the five-block tuple. -/
def physicalScoreCoordinates (d : ℕ) (s : Fin 8 → ℕ)
    (U : Matrix (LogicalIndex d) (LogicalIndex d) ℂ) (x : PhysicalBlocks d s) :
    PhysicalScoreCoordinateIndex d s → ℝ :=
  Sum.elim (complexRealCoordEquiv (LogicalIndex d × LogicalIndex d) (fun q => U q.1 q.2))
    (physicalCoordinatesEquiv d s x)

/-- The exact global amplitude polynomial, with the same exchange and output
regrouping as the operational channel. No physical hypothesis is needed. -/
def physicalGlobalPolynomial (d : ℕ) (s : Fin 8 → ℕ) :
    Matrix ((LogicalIndex d) × PhysicalEnvironmentIndex s) (LogicalIndex d)
      (ComplexPair (PhysicalScoreCoordinateIndex d s)) :=
  let VA := ComplexPair.matrixVariable (liftPhysicalScoreCoordinates (encoderACoordinates d s))
  let VB := ComplexPair.matrixVariable (liftPhysicalScoreCoordinates (encoderBCoordinates d s))
  let DA := ComplexPair.matrixVariable (liftPhysicalScoreCoordinates (decoderACoordinates d s))
  let DB := ComplexPair.matrixVariable (liftPhysicalScoreCoordinates (decoderBCoordinates d s))
  let J := ComplexPair.resourceInsert (ιA := Fin d) (ιB := Fin d)
    (liftPhysicalScoreCoordinates (resourceCoordinates d s))
  let encoded := ComplexPair.matrixMultiply (ComplexPair.matrixKronecker VA VB) J
  let exchanged := encoded.submatrix
    (exchangeEquiv (Fin (s 2)) (Fin (s 4)) (Fin (s 3)) (Fin (s 5))) id
  let joint := ComplexPair.matrixMultiply (ComplexPair.matrixKronecker DA DB) exchanged
  joint.submatrix (outputRegroup (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7))) id

/-- Every exact raw global amplitude has total degree at most five. -/
theorem physicalGlobalPolynomial_degree_le (d : ℕ) (s : Fin 8 → ℕ) :
    ∀ i j, ComplexPair.DegreeLE 5 (physicalGlobalPolynomial d s i j) := by
  let VA := ComplexPair.matrixVariable (liftPhysicalScoreCoordinates (encoderACoordinates d s))
  let VB := ComplexPair.matrixVariable (liftPhysicalScoreCoordinates (encoderBCoordinates d s))
  let DA := ComplexPair.matrixVariable (liftPhysicalScoreCoordinates (decoderACoordinates d s))
  let DB := ComplexPair.matrixVariable (liftPhysicalScoreCoordinates (decoderBCoordinates d s))
  let J := ComplexPair.resourceInsert (ιA := Fin d) (ιB := Fin d)
    (liftPhysicalScoreCoordinates (resourceCoordinates d s))
  have henc : ∀ i j, ComplexPair.DegreeLE 3
      (ComplexPair.matrixMultiply (ComplexPair.matrixKronecker VA VB) J i j) :=
    ComplexPair.degree_matrixMultiply _ _
      (ComplexPair.degree_matrixKronecker _ _ (ComplexPair.degree_matrixVariable _)
        (ComplexPair.degree_matrixVariable _)) (ComplexPair.degree_resourceInsert _)
  have hdec : ∀ i j, ComplexPair.DegreeLE 2 (ComplexPair.matrixKronecker DA DB i j) :=
    ComplexPair.degree_matrixKronecker _ _ (ComplexPair.degree_matrixVariable _)
      (ComplexPair.degree_matrixVariable _)
  have hglobal := ComplexPair.degree_matrixMultiply _ _ hdec
    (fun i j => henc
      (exchangeEquiv (Fin (s 2)) (Fin (s 4)) (Fin (s 3)) (Fin (s 5)) i) j)
  exact fun i j => hglobal
    (outputRegroup (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7)) i) j

/-- Evaluation is the production global matrix, not an abstract polynomial
map supplied by a representation premise. -/
theorem physicalGlobalPolynomial_evaluate (d : ℕ) (s : Fin 8 → ℕ)
    (U : Matrix (LogicalIndex d) (LogicalIndex d) ℂ) (x : PhysicalBlocks d s) :
    ComplexPair.evaluateMatrix (physicalScoreCoordinates d s U x) (physicalGlobalPolynomial d s) =
      globalIsometryRegrouped x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  simp only [physicalGlobalPolynomial, ComplexPair.evaluateMatrix_submatrix,
    ComplexPair.evaluateMatrix_matrixMultiply, ComplexPair.evaluateMatrix_matrixKronecker,
    ComplexPair.evaluateMatrix_matrixVariable, ComplexPair.evaluateMatrix_resourceInsert]
  change ((x.2.2.2.1 ⊗ₖ x.2.2.2.2) *
    ((x.2.1 ⊗ₖ x.2.2.1) * insertResource (Fin d) (Fin d) x.1).submatrix
      (exchangeEquiv (Fin (s 2)) (Fin (s 4)) (Fin (s 3)) (Fin (s 5))) id).submatrix
        (outputRegroup (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7))) id = _
  rw [← exchangeMatrix_mul]
  rfl

/-- Unnormalized target overlap for each discarded-environment slice. -/
def physicalOverlapPolynomial (d : ℕ) (s : Fin 8 → ℕ) (e : PhysicalEnvironmentIndex s) :
    ComplexPair (PhysicalScoreCoordinateIndex d s) :=
  ComplexPair.sum (fun p : LogicalIndex d × LogicalIndex d =>
    ComplexPair.multiply
      (ComplexPair.conjugate (ComplexPair.matrixVariable (targetScoreCoordinates d s) p.1 p.2))
      (physicalGlobalPolynomial d s (p.1, e) p.2))

theorem physicalOverlapPolynomial_degree_le (d : ℕ) (s : Fin 8 → ℕ)
    (e : PhysicalEnvironmentIndex s) :
    ComplexPair.DegreeLE 6 (physicalOverlapPolynomial d s e) :=
  ComplexPair.degree_sum _ (fun p => ComplexPair.degree_multiply
    (ComplexPair.degree_conjugate (ComplexPair.degree_matrixVariable _ p.1 p.2))
    (physicalGlobalPolynomial_degree_le d s (p.1, e) p.2))

theorem physicalOverlapPolynomial_evaluate (d : ℕ) (s : Fin 8 → ℕ)
    (U : Matrix (LogicalIndex d) (LogicalIndex d) ℂ) (x : PhysicalBlocks d s)
    (e : PhysicalEnvironmentIndex s) :
    ComplexPair.evaluate (physicalScoreCoordinates d s U x) (physicalOverlapPolynomial d s e) =
      frobInner U (sliceAt
        (globalIsometryRegrouped x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) e) := by
  rw [frobInner_eq_sum_prod]
  simp only [physicalOverlapPolynomial, ComplexPair.evaluate_sum,
    ComplexPair.evaluate_multiply, ComplexPair.evaluate_conjugate, sliceAt_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hglobal := congrArg (fun M => M (p.1, e) p.2)
    (physicalGlobalPolynomial_evaluate d s U x)
  change star (ComplexPair.evaluate (physicalScoreCoordinates d s U x)
      (ComplexPair.matrixVariable (targetScoreCoordinates d s) p.1 p.2)) *
    ComplexPair.evaluate (physicalScoreCoordinates d s U x)
      (physicalGlobalPolynomial d s (p.1, e) p.2) = _
  rw [show ComplexPair.evaluate (physicalScoreCoordinates d s U x)
      (ComplexPair.matrixVariable (targetScoreCoordinates d s) p.1 p.2) = U p.1 p.2 by
    dsimp only [ComplexPair.matrixVariable, Matrix.of_apply]
    rw [ComplexPair.evaluate_coordinatePair]
    rfl]
  exact congrArg (fun z => star (U p.1 p.2) * z) hglobal

/-- A constructed integer polynomial for the target-score numerator. -/
def physicalScoreNumeratorPolynomial (d : ℕ) (s : Fin 8 → ℕ) :
    MvPolynomial (PhysicalScoreCoordinateIndex d s) ℤ :=
  ∑ e : PhysicalEnvironmentIndex s, ComplexPair.normSquare (physicalOverlapPolynomial d s e)

/-- The variable-target score numerator has total degree at most twelve. -/
theorem physicalScoreNumeratorPolynomial_degree_le (d : ℕ) (s : Fin 8 → ℕ) :
    (physicalScoreNumeratorPolynomial d s).totalDegree ≤ 12 :=
  totalDegree_finsetSum_le (fun e _ =>
    ComplexPair.degree_normSquare (physicalOverlapPolynomial_degree_le d s e))

/-- Clearing the normalized Choi denominator for a nonempty input. -/
theorem scoreU_channelOf_clear_denominator {ι κ ε : Type*}
    [Fintype ι] [Fintype κ] [Fintype ε]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq ε]
    (hι : 0 < Fintype.card ι) (U : Matrix κ ι ℂ) (F : Matrix (κ × ε) ι ℂ) :
    (Fintype.card ι : ℝ) ^ 2 * scoreU U (channelOf F) =
      ∑ e, Complex.normSq (frobInner U (sliceAt F e)) := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hι
  rw [scoreU_channelOf]
  simp only [Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_natCast]
  rw [← Finset.mul_sum, ← pow_two, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero 2 hcard), one_mul]

/-- Exact integer-polynomial equality for the normalized score on the
entire five-block space. The factor is `d⁴`, not `d²`, because the logical
input dimension is `d²`. Arbitrary targets are parameters, not rational
constants silently inserted into the coefficients. -/
theorem physicalScoreNumeratorPolynomial_evaluate {d : ℕ} (hd : 0 < d)
    (s : Fin 8 → ℕ) (U : Matrix (LogicalIndex d) (LogicalIndex d) ℂ)
    (x : PhysicalBlocks d s) :
    eval (physicalScoreCoordinates d s U x) (physicalScoreNumeratorPolynomial d s) =
      (d : ℝ) ^ 4 * physicalScore U x := by
  have hcard : 0 < Fintype.card (LogicalIndex d) := by
    simpa only [LogicalIndex, Fintype.card_prod, Fintype.card_fin] using Nat.mul_pos hd hd
  calc
    eval (physicalScoreCoordinates d s U x) (physicalScoreNumeratorPolynomial d s) =
        ∑ e : PhysicalEnvironmentIndex s, Complex.normSq (frobInner U (sliceAt
          (globalIsometryRegrouped x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) e)) := by
      simp only [physicalScoreNumeratorPolynomial, map_sum, ComplexPair.eval_normSquare,
        physicalOverlapPolynomial_evaluate]
    _ = (Fintype.card (LogicalIndex d) : ℝ) ^ 2 *
        scoreU U (channelOf
          (globalIsometryRegrouped x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)) :=
      (scoreU_channelOf_clear_denominator hcard U _).symm
    _ = (d : ℝ) ^ 4 * physicalScore U x := by
      simp only [LogicalIndex, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
        physicalScore, operationalChannel]
      ring

end NLQCLean.PhysicalPolynomial

end

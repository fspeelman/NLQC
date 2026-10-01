import NLQCLean.Arithmetic.PhysicalScorePolynomial
import NLQCLean.Invariants.ControlledPhase
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Integer target-score polynomials for two real phase parameters

Substituting the corner phase `diag(1,1,1,c + i t)` into the generic
score numerator leaves exactly two target coordinates. The polynomial has
integer coefficients and degree at most twelve; its evaluation is sixteen
times the normalized score. This is a raw polynomial identity, not a
coefficient-height, elimination or named-target separation result.
-/

noncomputable section

namespace NLQCLean.PhysicalPolynomial

attribute [local implicit_reducible] Matrix

open Matrix MvPolynomial
open scoped BigOperators

/-- Substitution by polynomials of degree at most one cannot increase total
degree. The proof uses the finite monomial expansion. -/
theorem totalDegree_bind₁_le_of_linear_variables {σ τ : Type*}
    (f : σ → MvPolynomial τ ℤ) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (p : MvPolynomial σ ℤ) : (bind₁ f p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  rw [bind₁, aeval_monomial]
  apply (totalDegree_mul _ _).trans
  simp only [algebraMap_eq, totalDegree_C, zero_add]
  change (∏ i ∈ d.support, f i ^ d i).totalDegree ≤ p.totalDegree
  apply (totalDegree_finsetProd _ _).trans
  calc
    (∑ i ∈ d.support, (f i ^ d i).totalDegree) ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hf i))
    _ = d.sum (fun _ e => e) := rfl
    _ ≤ p.totalDegree := le_totalDegree hd

/-- Real evaluation of the integer substitution is exactly composition. -/
theorem eval_bind₁ {σ τ : Type*} (x : τ → ℝ)
    (f : σ → MvPolynomial τ ℤ) (p : MvPolynomial σ ℤ) :
    eval x (bind₁ f p) = eval (fun i => eval x (f i)) p :=
  eval₂Hom_bind₁ (Int.castRingHom ℝ) x f p

/-- Two phase parameters, separately from all physical entries. -/
abbrev PhaseScoreCoordinateIndex (s : Fin 8 → ℕ) := Fin 2 ⊕ PhysicalCoordinateIndex 2 s

theorem card_phaseScoreCoordinateIndex (s : Fin 8 → ℕ) :
    Fintype.card (PhaseScoreCoordinateIndex s) = physicalRawRealCoordinateCount 2 s + 2 := by
  rw [Fintype.card_sum, card_physicalCoordinateIndex]
  simp only [Fintype.card_fin, Nat.add_comm]

/-- The real and imaginary entries of the corner target, represented
only by integer constants and the two phase variables. -/
def phaseScoreSubstitution (s : Fin 8 → ℕ) :
    PhysicalScoreCoordinateIndex 2 s → MvPolynomial (PhaseScoreCoordinateIndex s) ℤ :=
  Sum.elim
    (fun q => if q.1.1 = q.1.2 then
      if q.1.1 = (1, 1) then X (Sum.inl q.2)
        else if q.2 = 0 then 1 else 0
      else 0)
    (fun q => X (Sum.inr q))

theorem phaseScoreSubstitution_degree_le (s : Fin 8 → ℕ)
    (q : PhysicalScoreCoordinateIndex 2 s) : (phaseScoreSubstitution s q).totalDegree ≤ 1 := by
  rcases q with q | q
  · dsimp [phaseScoreSubstitution]
    split_ifs <;> simp
  · simp [phaseScoreSubstitution]

def phaseScoreCoordinates (s : Fin 8 → ℕ) (c t : ℝ) (x : PhysicalBlocks 2 s) :
    PhaseScoreCoordinateIndex s → ℝ := Sum.elim ![c, t] (physicalCoordinatesEquiv 2 s x)

/-- Evaluation of every substituted coordinate is the coordinate of the
corner phase and the unchanged physical tuple. -/
theorem phaseScoreSubstitution_evaluate (s : Fin 8 → ℕ) (c t : ℝ)
    (x : PhysicalBlocks 2 s) :
    (fun q => eval (phaseScoreCoordinates s c t x) (phaseScoreSubstitution s q)) =
      physicalScoreCoordinates 2 s (qubitCornerPhase ⟨c, t⟩) x := by
  funext q
  rcases q with ⟨⟨i, j⟩, b⟩ | q
  · by_cases hij : i = j
    · subst j
      by_cases hi : i = (1, 1)
      · subst i
        fin_cases b <;>
          simp [phaseScoreSubstitution, phaseScoreCoordinates, physicalScoreCoordinates,
            complexRealCoordEquiv, qubitCornerPhase, Matrix.diagonal_apply, eval]
      · fin_cases b <;>
          simp [phaseScoreSubstitution, phaseScoreCoordinates, physicalScoreCoordinates,
            complexRealCoordEquiv, qubitCornerPhase, Matrix.diagonal_apply, hi, eval]
    · fin_cases b <;>
        simp [phaseScoreSubstitution, phaseScoreCoordinates, physicalScoreCoordinates,
          complexRealCoordEquiv, qubitCornerPhase, Matrix.diagonal_apply, hij, eval]
  · simp [phaseScoreSubstitution, phaseScoreCoordinates, physicalScoreCoordinates, eval]

/-- The two-parameter score numerator has integer coefficients. -/
def controlledPhaseScoreNumeratorPolynomial (s : Fin 8 → ℕ) :
    MvPolynomial (PhaseScoreCoordinateIndex s) ℤ :=
  bind₁ (phaseScoreSubstitution s) (physicalScoreNumeratorPolynomial 2 s)

theorem controlledPhaseScoreNumeratorPolynomial_degree_le (s : Fin 8 → ℕ) :
    (controlledPhaseScoreNumeratorPolynomial s).totalDegree ≤ 12 :=
  (totalDegree_bind₁_le_of_linear_variables _ (phaseScoreSubstitution_degree_le s) _).trans
    (physicalScoreNumeratorPolynomial_degree_le 2 s)

/-- Exact normalized-score equality for arbitrary phase parameters and every
five-block tuple, without a unit-circle or physical premise. -/
theorem controlledPhaseScoreNumeratorPolynomial_evaluate (s : Fin 8 → ℕ)
    (c t : ℝ) (x : PhysicalBlocks 2 s) :
    eval (phaseScoreCoordinates s c t x) (controlledPhaseScoreNumeratorPolynomial s) =
      16 * physicalScore (qubitCornerPhase ⟨c, t⟩) x := by
  rw [controlledPhaseScoreNumeratorPolynomial, eval_bind₁, phaseScoreSubstitution_evaluate]
  simpa only [Nat.cast_ofNat, show (2 : ℝ) ^ 4 = 16 by norm_num] using
    physicalScoreNumeratorPolynomial_evaluate (by decide : 0 < 2) s (qubitCornerPhase ⟨c, t⟩) x

/-- The same polynomial applies to the existing exponential controlled-phase
target. No arithmetic property of the fixed trigonometric values is assumed. -/
theorem controlledPhaseScoreNumeratorPolynomial_evaluate_angle (s : Fin 8 → ℕ)
    (θ : ℝ) (x : PhysicalBlocks 2 s) :
    eval (phaseScoreCoordinates s (Real.cos θ) (Real.sin θ) x)
        (controlledPhaseScoreNumeratorPolynomial s) =
      16 * physicalScore (controlledPhase θ) x := by
  rw [controlledPhaseScoreNumeratorPolynomial_evaluate]
  congr 2
  change qubitCornerPhase ⟨Real.cos θ, Real.sin θ⟩ =
    qubitCornerPhase (Complex.exp ((θ : ℂ) * Complex.I))
  congr 1
  rw [Complex.exp_mul_I]
  apply Complex.ext <;> simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]

end NLQCLean.PhysicalPolynomial

end

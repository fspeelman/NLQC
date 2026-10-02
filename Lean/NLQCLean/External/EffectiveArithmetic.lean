/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Basic.Sign.Basic
import Mathlib.RingTheory.Algebraic.Defs

/-!
# External inputs for the effective explicit-gate bound

Two published theorems used by Appendix C (`thm:explicit`) of the robust
companion, stated as transparent propositions. Neither is assumed globally;
each is an explicit argument of the conditional theorems that use it. Source
locators and the fidelity review are recorded in `docs/EXTERNAL_RESULTS.md`
(E-QE and E-TM).

* `BasuPollackRoyExistentialElimination`: Basu–Pollack–Roy, *Algorithms in
  Real Algebraic Geometry*, 2nd ed., Theorem 14.16 (printed pp. 550–551),
  specialized to one existential block, two free variables and integer
  coefficients. The book's `d^{O(k)}` and `τ d^{O(k)O(ℓ)}` bounds are expressed
  by one absolute constant `a` as `d^{a(k+1)}` and `τ d^{a(k+1)}`.
* `CijsouwTranscendenceMeasureExp`: Cijsouw, Compositio Math. 28 (1974),
  Theorem 1 (printed p. 164): `exp(-C N² (N + log H))` is a transcendence measure
  of `e^α` for every nonzero algebraic `α`.
* `PolynomialTypeTranscendenceMeasureExpAngle`: the weaker polynomial-type
  measure `exp(-C (N + log H)^c)` for `e^{iθ}`, `θ ≠ 0` real algebraic, which is
  the form Appendix C cites and the only form `thm:explicit` uses.

The sources also assert that the constants are effectively computable; that
assertion is not encoded, so the conditional theorems prove existence of
their constants only.
-/

namespace NLQCLean

/-- Every integer coefficient has bit size at most `τ`, i.e. absolute value
below `2^τ`. -/
def IntPolynomialBitsizeLE {σ : Type*} (p : MvPolynomial σ ℤ) (τ : ℕ) : Prop :=
  ∀ m, (p.coeff m).natAbs < 2 ^ τ

/-- A sign condition `sign Q(y) = σ` on an integer polynomial in `n` variables. -/
structure IntSignAtom (n : ℕ) where
  polynomial : MvPolynomial (Fin n) ℤ
  sign : SignType

/-- Evaluation of a sign condition at a real point. -/
def IntSignAtom.Holds {n : ℕ} (A : IntSignAtom n) (y : Fin n → ℝ) : Prop :=
  SignType.sign (MvPolynomial.eval₂ (Int.castRingHom ℝ) y A.polynomial) = A.sign

/-- A finite disjunction of finite conjunctions of integer sign conditions. -/
abbrev IntSignDNF (n : ℕ) := List (List (IntSignAtom n))

/-- Truth of a quantifier-free sign formula at a real point. -/
def IntSignDNF.Holds {n : ℕ} (Ψ : IntSignDNF n) (y : Fin n → ℝ) : Prop :=
  ∃ L ∈ Ψ, ∀ A ∈ L, A.Holds y

/-- **E-QE.** BPR Theorem 14.16 for one existential block of `k = card ι`
variables and `ℓ = 2` free variables. For any `s` integer polynomials of total
degree at most `d ≥ 2` and coefficient bit size at most `τ ≥ 1`, and any
Boolean combination `F` of their sign conditions, the formula
`∃ x, F(sign P₁(y,x), …, sign Pₛ(y,x))` is equivalent to a disjunction of
conjunctions of sign conditions on integer polynomials in `y` of total degree
at most `d^{a(k+1)}` and coefficient bit size at most `τ d^{a(k+1)}`, for one
absolute constant `a`. -/
def BasuPollackRoyExistentialElimination : Prop :=
  ∃ a : ℕ, ∀ (ι : Type) [Fintype ι] (s d τ : ℕ), 2 ≤ d → 1 ≤ τ →
    ∀ P : Fin s → MvPolynomial (Fin 2 ⊕ ι) ℤ,
      (∀ i, (P i).totalDegree ≤ d) → (∀ i, IntPolynomialBitsizeLE (P i) τ) →
      ∀ F : (Fin s → SignType) → Prop,
        ∃ Ψ : IntSignDNF 2,
          (∀ L ∈ Ψ, ∀ A ∈ L,
            A.polynomial.totalDegree ≤ d ^ (a * (Fintype.card ι + 1)) ∧
            IntPolynomialBitsizeLE A.polynomial (τ * d ^ (a * (Fintype.card ι + 1)))) ∧
          ∀ y : Fin 2 → ℝ, Ψ.Holds y ↔ ∃ x : ι → ℝ,
            F (fun i => SignType.sign
              (MvPolynomial.eval₂ (Int.castRingHom ℝ) (Sum.elim y x) (P i)))

/-- **E-TM.** Cijsouw 1974, Theorem 1. For every nonzero algebraic `α` there is
`C > 0` such that every nonconstant integer polynomial `P` of degree at most `N`
whose coefficients have absolute value at most `H` satisfies
`|P(e^α)| > exp(-C N² (N + log H))`. -/
def CijsouwTranscendenceMeasureExp : Prop :=
  ∀ α : ℂ, α ≠ 0 → IsAlgebraic ℚ α →
    ∃ C : ℝ, 0 < C ∧ ∀ (N H : ℕ) (P : Polynomial ℤ), 0 < P.natDegree → P.natDegree ≤ N →
      (∀ i, |P.coeff i| ≤ (H : ℤ)) →
        Real.exp (-(C * (N : ℝ) ^ 2 * ((N : ℝ) + Real.log H))) <
          ‖P.eval₂ (Int.castRingHom ℂ) (Complex.exp α)‖

/-- **E-TM, weak form.** For every nonzero real algebraic `θ`, `e^{iθ}` has a
transcendence measure of polynomial type: there are `C > 0` and an exponent `c`
such that every nonconstant integer polynomial `P` of degree at most `N` whose
coefficients have absolute value at most `H` satisfies
`|P(e^{iθ})| ≥ exp(-C (N + log H)^c)`. Cijsouw's theorem implies it with `c = 3`
(`CijsouwTranscendenceMeasureExp.polynomialType`). This is the only form used
by `thm:explicit`. -/
def PolynomialTypeTranscendenceMeasureExpAngle : Prop :=
  ∀ θ : ℝ, θ ≠ 0 → IsAlgebraic ℚ θ →
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧ ∀ (N H : ℕ) (P : Polynomial ℤ), 0 < P.natDegree →
      P.natDegree ≤ N → (∀ i, |P.coeff i| ≤ (H : ℤ)) →
        Real.exp (-(C * ((N : ℝ) + Real.log H) ^ c)) ≤
          ‖P.eval₂ (Int.castRingHom ℂ) (Complex.exp ((θ : ℂ) * Complex.I))‖

end NLQCLean

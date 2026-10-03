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

Transcendence measures for Appendix C (`thm:explicit`) of the robust companion, stated as
transparent propositions. Neither is assumed globally. The weak form is proved in
`Arithmetic/GelfondAngleMeasure`; the `_of_transcendenceMeasure` theorems take it as an
explicit argument. Source locators and the fidelity review are recorded in
`docs/EXTERNAL_RESULTS.md` (E-TM).

* `CijsouwTranscendenceMeasureExp`: Cijsouw, Compositio Math. 28 (1974),
  Theorem 1 (printed p. 164): `exp(-C N² (N + log H))` is a transcendence measure
  of `e^α` for every nonzero algebraic `α`.
* `PolynomialTypeTranscendenceMeasureExpAngle`: the weaker polynomial-type
  measure `exp(-C (N + log H)^c)` for `e^{iθ}`, `θ ≠ 0` real algebraic, which is
  the form Appendix C cites and the only form `thm:explicit` uses.

The sources also assert that the constants are effectively computable; that
assertion is not encoded. `IntPolynomialBitsizeLE` is the bit-size predicate used by the
eliminant bounds.
-/

namespace NLQCLean

/-- Every integer coefficient has bit size at most `τ`, i.e. absolute value
below `2^τ`. -/
def IntPolynomialBitsizeLE {σ : Type*} (p : MvPolynomial σ ℤ) (τ : ℕ) : Prop :=
  ∀ m, (p.coeff m).natAbs < 2 ^ τ

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

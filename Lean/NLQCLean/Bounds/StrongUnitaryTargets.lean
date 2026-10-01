import NLQCLean.Models.DiamondReachability
import NLQCLean.Models.SwapNeighborhood
import NLQCLean.Geometry.UnitaryHaar
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Strong unitary bound statements

Named propositions for the restricted near-SWAP Haar estimates and their
universal resource consequences, proved in the strong-bound modules.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius ENNReal

theorem measurableSet_swapNeighborhood (d : ℕ) : MeasurableSet (swapNeighborhood d) :=
  (isClosed_swapNeighborhood d).measurableSet

/-- Near-SWAP patch mass: `μ_d(S_d) ≥ exp(−C₀ N)` for every `d ≥ 2`. -/
def StrongSwapPatchMassBound (C₀ : ℝ) : Prop :=
  ∀ d : ℕ, 2 ≤ d →
    ENNReal.ofReal (Real.exp (-(C₀ * (d : ℝ) ^ 4))) ≤
      unitaryHaar (Fin d × Fin d) (swapNeighborhood d)

/-- Near-SWAP score Haar bound: the restricted score Haar estimate, pure and finite mixed, for `K ≥ D/2`,
`0 < e ≤ 1/2`, with exponent `N/16`. Haar is not renormalized on `S_d`. -/
def StrongRestrictedHaarBound (C : ℝ) : Prop :=
  ∀ d K : ℕ, 2 ≤ d → (d : ℝ) ^ 2 / 2 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
    unitaryHaar (Fin d × Fin d) (swapNeighborhood d ∩ pureReachable d K e) ≤
        min 1 (ENNReal.ofReal (Real.exp (C * (K : ℝ) ^ 2) * e ^ ((d : ℝ) ^ 4 / 16))) ∧
      unitaryHaar (Fin d × Fin d) (swapNeighborhood d ∩ mixedReachable d K e) ≤
        min 1 (ENNReal.ofReal (Real.exp (C * (K : ℝ) ^ 2) * e ^ ((d : ℝ) ^ 4 / 16)))

/-- Near-SWAP diamond Haar bound: the same restricted estimate for diamond reachability, as Haar outer measure. -/
def StrongRestrictedDiamondHaarBound (C : ℝ) : Prop :=
  ∀ d K : ℕ, 2 ≤ d → (d : ℝ) ^ 2 / 2 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
    (unitaryHaar (Fin d × Fin d)).toOuterMeasure
        (swapNeighborhood d ∩ pureDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e) ≤
        min 1 (ENNReal.ofReal (Real.exp (C * (K : ℝ) ^ 2) * e ^ ((d : ℝ) ^ 4 / 16))) ∧
      (unitaryHaar (Fin d × Fin d)).toOuterMeasure
        (swapNeighborhood d ∩ mixedDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e) ≤
        min 1 (ENNReal.ofReal (Real.exp (C * (K : ℝ) ^ 2) * e ^ ((d : ℝ) ^ 4 / 16)))

/-- Universal pure/mixed score implementation forces `K ≥ c d² √log(1/e)`. -/
def StrongUniversalResourceBound (c : ℝ) : Prop :=
  ∀ d K : ℕ, 2 ≤ d → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
    (PureUniversalScore d K e → c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (MixedUniversalScore d K e → c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K)

/-- The same for universal pure/mixed normalized diamond implementation. -/
def StrongUniversalDiamondResourceBound (c : ℝ) : Prop :=
  ∀ d K : ℕ, 2 ≤ d → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
    (PureUniversalDiamond.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (MixedUniversalDiamond.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K)

/-- At `d = 2ⁿ`, `log₂ K ≥ 2n + ½ log₂ log(1/e) − b`. -/
def StrongUniversalQubitBound (b : ℝ) : Prop :=
  ∀ n K : ℕ, 1 ≤ n → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
    (PureUniversalScore (2 ^ n) K e →
        2 * (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
      (MixedUniversalScore (2 ^ n) K e →
        2 * (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ))

/-- The qubit form for universal normalized diamond implementation. -/
def StrongUniversalDiamondQubitBound (b : ℝ) : Prop :=
  ∀ n K : ℕ, 1 ≤ n → 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
    (PureUniversalDiamond.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
        2 * (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
      (MixedUniversalDiamond.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
        2 * (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ))

end NLQCLean

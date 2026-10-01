import NLQCLean.Arithmetic.PolynomialBoundary
import NLQCLean.Semialgebraic.RationalSignDiagrams
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Localization.Integral

/-!
# Algebraic points of rational semialgebraic null sets

Boolean rational sign descriptions are locally constant away from the zeroes
of their nonzero defining polynomials. At a member of a null set this local
constancy is impossible, so a nonzero rational polynomial vanishes there.
In one coordinate its univariate form certifies algebraicity.

The scalar and Euclidean statements each use the measure of the actual set
appearing in that statement. No coordinate measure transport, component
finiteness, or quantifier-elimination premise is needed.
-/

namespace NLQCLean.RationalQE

open Filter MeasureTheory
open scoped Topology

/-- A rational Boolean sign description is locally constant at a point, or
a nonzero rational defining polynomial vanishes at that point. The continuous
coordinate map permits both scalar and Euclidean applications. -/
theorem SADef.eventually_mem_iff_or_exists_nonzero_rational_polynomial_zero
    {n : ℕ} {S : Set (Fin n → ℝ)} (hS : SADef n S)
    {X : Type*} [TopologicalSpace X] (g : X → Fin n → ℝ)
    (hg : Continuous g) (x : X) :
    (∀ᶠ y in 𝓝 x, g y ∈ S ↔ g x ∈ S) ∨
      ∃ p : MvPolynomial (Fin n) ℝ,
        p ∈ rationalPolynomialSubring (Fin n) ∧ p ≠ 0 ∧
          MvPolynomial.eval (g x) p = 0 := by
  induction hS with
  | pos p hp =>
    by_cases hp0 : p = 0
    · left
      exact Eventually.of_forall (fun y => by simp [hp0])
    by_cases hpx : MvPolynomial.eval (g x) p = 0
    · exact Or.inr ⟨p, hp, hp0, hpx⟩
    · left
      have he := ((p.continuous_eval.comp hg).tendsto x).eventually
        (PolynomialSign.eventually_same hpx)
      filter_upwards [he] with y hy
      exact hy PolynomialSign.positive
  | compl _ ih =>
    rcases ih with hstable | hroot
    · left
      filter_upwards [hstable] with y hy
      exact not_congr hy
    · exact Or.inr hroot
  | union _ _ ihS ihT =>
    rcases ihS with hstableS | hroot
    · rcases ihT with hstableT | hroot
      · left
        filter_upwards [hstableS, hstableT] with y hyS hyT
        exact or_congr hyS hyT
      · exact Or.inr hroot
    · exact Or.inr hroot

/-- A member of a null continuous pullback of a rational sign description
zeros a nonzero rational polynomial. Identically zero atoms do not provide
the witness. -/
theorem SADef.exists_nonzero_rational_polynomial_zero_of_measure_eq_zero
    {n : ℕ} {S : Set (Fin n → ℝ)} (hS : SADef n S)
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (g : X → Fin n → ℝ) (hg : Continuous g) (μ : Measure X)
    [Measure.IsOpenPosMeasure μ] (hnull : μ (g ⁻¹' S) = 0)
    {x : X} (hx : g x ∈ S) :
    ∃ p : MvPolynomial (Fin n) ℝ,
      p ∈ rationalPolynomialSubring (Fin n) ∧ p ≠ 0 ∧
        MvPolynomial.eval (g x) p = 0 := by
  rcases hS.eventually_mem_iff_or_exists_nonzero_rational_polynomial_zero g hg x with
    hstable | hroot
  · have hi : x ∈ interior (g ⁻¹' S) :=
      (mem_interior_iff_mem_nhds).mpr
        (hstable.mono fun _ h => h.mpr hx)
    have hp := μ.measure_pos_of_nonempty_interior ⟨x, hi⟩
    rw [hnull] at hp
    exact (lt_irrefl _ hp).elim
  · exact hroot

/-- A nonzero rational one-variable polynomial is an algebraicity witness
for its real root. The coefficient-extension witness and the one-variable
algebra equivalence preserve the nonzero polynomial explicitly. -/
theorem isAlgebraic_of_nonzero_rational_polynomial_zero
    {p : MvPolynomial (Fin 1) ℝ}
    (hpr : p ∈ rationalPolynomialSubring (Fin 1)) (hp : p ≠ 0)
    {x : Fin 1 → ℝ} (hx : MvPolynomial.eval x p = 0) :
    IsAlgebraic ℚ (x 0) := by
  obtain ⟨q, hq⟩ := mem_rationalPolynomialSubring_iff p |>.mp hpr
  have hq0 : q ≠ 0 := by
    intro h
    apply hp
    rw [← hq, h, map_zero]
  refine ⟨MvPolynomial.uniqueAlgEquiv ℚ (Fin 1) q, ?_, ?_⟩
  · intro h
    apply hq0
    apply (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).injective
    simpa only [map_zero] using h
  · change Polynomial.eval₂ (algebraMap ℚ ℝ) (x 0)
      (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1) q) = 0
    rw [← show x (default : Fin 1) = x 0 from congrArg x (Subsingleton.elim _ _),
      MvPolynomial.eval₂_uniqueAlgEquiv (a := x)]
    rw [← MvPolynomial.eval_map, hq]
    exact hx

/-- Every point of a rational semialgebraic scalar null set is algebraic
over the rationals. This uses scalar Lebesgue measure directly. -/
theorem SADef.isAlgebraic_of_scalar_measure_eq_zero
    {S : Set (Fin 1 → ℝ)} (hS : SADef 1 S)
    (hnull : volume {t : ℝ | (fun _ : Fin 1 => t) ∈ S} = 0)
    {t : ℝ} (ht : (fun _ : Fin 1 => t) ∈ S) : IsAlgebraic ℚ t := by
  obtain ⟨p, hpr, hp, hpt⟩ :=
    hS.exists_nonzero_rational_polynomial_zero_of_measure_eq_zero
      (fun t : ℝ => fun _ : Fin 1 => t) (by fun_prop) volume hnull ht
  exact isAlgebraic_of_nonzero_rational_polynomial_zero hpr hp hpt

/-- Integer-polynomial algebraicity of every point of the same scalar null set. -/
theorem SADef.isAlgebraic_int_of_scalar_measure_eq_zero
    {S : Set (Fin 1 → ℝ)} (hS : SADef 1 S)
    (hnull : volume {t : ℝ | (fun _ : Fin 1 => t) ∈ S} = 0)
    {t : ℝ} (ht : (fun _ : Fin 1 => t) ∈ S) : IsAlgebraic ℤ t :=
  (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr
    (hS.isAlgebraic_of_scalar_measure_eq_zero hnull ht)

/-- Every point of a rational semialgebraic null set in one Euclidean
coordinate has an algebraic coordinate. Nullity is measured in that actual
Euclidean set, so this theorem needs no scalar-volume adapter. -/
theorem SADef.isAlgebraic_of_euclidean_measure_eq_zero
    {S : Set (Fin 1 → ℝ)} (hS : SADef 1 S)
    (hnull : volume {x : RealEuclidean 1 | WithLp.ofLp x ∈ S} = 0)
    {x : RealEuclidean 1} (hx : WithLp.ofLp x ∈ S) :
    IsAlgebraic ℚ (x 0) := by
  obtain ⟨p, hpr, hp, hpx⟩ :=
    hS.exists_nonzero_rational_polynomial_zero_of_measure_eq_zero
      (fun y : RealEuclidean 1 => fun i => y i) (by fun_prop) volume hnull hx
  exact isAlgebraic_of_nonzero_rational_polynomial_zero hpr hp hpx

/-- Integer-polynomial version of the Euclidean-coordinate conclusion. -/
theorem SADef.isAlgebraic_int_of_euclidean_measure_eq_zero
    {S : Set (Fin 1 → ℝ)} (hS : SADef 1 S)
    (hnull : volume {x : RealEuclidean 1 | WithLp.ofLp x ∈ S} = 0)
    {x : RealEuclidean 1} (hx : WithLp.ofLp x ∈ S) :
    IsAlgebraic ℤ (x 0) :=
  (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr
    (hS.isAlgebraic_of_euclidean_measure_eq_zero hnull hx)

end NLQCLean.RationalQE

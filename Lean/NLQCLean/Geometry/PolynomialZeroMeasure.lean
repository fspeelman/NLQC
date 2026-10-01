/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Geometry.PolynomialCoefficients
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Nonzero polynomial zero sets have Lebesgue measure zero

Induction on the number of variables, using a nonzero coefficient,
finite univariate roots and Fubini. No semialgebraic external input is used.
-/

section

open MeasureTheory
open scoped ENNReal

namespace NLQCLean

/-- A nonzero real polynomial is nonzero almost everywhere in product coordinates. -/
theorem ae_mvPolynomial_eval_ne_zero {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    ∀ᵐ x : Fin n → ℝ, MvPolynomial.eval x p ≠ 0 := by
  induction n with
  | zero =>
    apply Filter.Eventually.of_forall
    intro x hx
    apply hp
    apply MvPolynomial.funext
    intro y
    rw [Subsingleton.elim y x]
    simpa using hx
  | succ n ih =>
    obtain ⟨i, hi⟩ := MvPolynomial.nonempty_support_finSuccEquiv hp
    have hi' := Polynomial.mem_support_iff.mp hi
    have hcoeff := ih ((MvPolynomial.finSuccEquiv ℝ n p).coeff i) hi'
    have hfib : ∀ᵐ x : Fin n → ℝ, ∀ᵐ t : ℝ,
        MvPolynomial.eval (Fin.cons t x) p ≠ 0 := by
      filter_upwards [hcoeff] with x hx
      let q := Polynomial.map (MvPolynomial.eval x) (MvPolynomial.finSuccEquiv ℝ n p)
      have hq : q ≠ 0 := by
        intro h
        have hz := congrArg (fun q : Polynomial ℝ => q.coeff i) h
        exact hx (by simpa [q] using hz)
      have hz := (Polynomial.finite_setOfPred_isRoot hq).measure_zero volume
      simpa only [ae_iff, not_not, MvPolynomial.eval_eq_eval_mv_eval', Polynomial.IsRoot]
        using hz
    have hc : Continuous (fun z : ℝ × (Fin n → ℝ) =>
        MvPolynomial.eval (Fin.cons z.1 z.2) p) := p.continuous_eval.comp (by fun_prop)
    have hm : MeasurableSet {z : ℝ × (Fin n → ℝ) |
        MvPolynomial.eval (Fin.cons z.1 z.2) p ≠ 0} :=
      (isClosed_singleton.preimage hc).isOpen_compl.measurableSet
    have hprod : ∀ᵐ z : ℝ × (Fin n → ℝ),
        MvPolynomial.eval (Fin.cons z.1 z.2) p ≠ 0 :=
      (Measure.ae_prod_iff_ae_ae hm).mpr ((Measure.ae_ae_comm hm).mpr hfib)
    have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).quasiMeasurePreserving.ae hprod
    simpa [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Fin.cons_self_tail]
      using h

/-- The zero set of a nonzero polynomial is null in the project's Euclidean volume. -/
theorem mvPolynomial_zeroSet_volume_eq_zero {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p ≠ 0) :
    volume {x : RealEuclidean n | MvPolynomial.eval (fun i => x i) p = 0} = 0 := by
  have h := (PiLp.volume_preserving_ofLp (Fin n)).quasiMeasurePreserving.ae
    (ae_mvPolynomial_eval_ne_zero p hp)
  simpa only [ae_iff, not_not] using h

end NLQCLean
end

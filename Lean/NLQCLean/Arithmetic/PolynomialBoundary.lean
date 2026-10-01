import NLQCLean.Semialgebraic.LocalSignStability
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Nonzero polynomial witnesses at sign-formula boundaries

Identically zero polynomials have constant signs and contribute no boundary
witness. These elementary topological certificates require neither effective
quantifier elimination nor a transcendence premise.
-/

namespace NLQCLean

open Filter
open scoped Topology

theorem PolynomialSignAtom.eventually_holds_iff {n : ℕ}
    (A : PolynomialSignAtom n) (x : RealEuclidean n)
    (hx : A.polynomial = 0 ∨ MvPolynomial.eval (fun i => x i) A.polynomial ≠ 0) :
    ∀ᶠ y in 𝓝 x, A.Holds y ↔ A.Holds x := by
  rcases hx with hp | he
  · exact Eventually.of_forall (fun y => by simp [PolynomialSignAtom.Holds, hp])
  · have hc : Continuous (fun y : RealEuclidean n =>
        MvPolynomial.eval (fun i => y i) A.polynomial) :=
      A.polynomial.continuous_eval.comp (by fun_prop)
    exact (hc.tendsto x).eventually (PolynomialSign.eventually_same he) |>.mono
      (fun y hy => hy A.sign)

theorem PolynomialSignDNF.eventually_clauseHolds_iff {n : ℕ}
    (L : List (PolynomialSignAtom n)) (x : RealEuclidean n)
    (hx : ∀ A ∈ L,
      A.polynomial = 0 ∨ MvPolynomial.eval (fun i => x i) A.polynomial ≠ 0) :
    ∀ᶠ y in 𝓝 x, PolynomialSignDNF.clauseHolds L y ↔
      PolynomialSignDNF.clauseHolds L x := by
  induction L with
  | nil => exact Eventually.of_forall (fun y => by simp)
  | cons A L ih =>
    have hA := A.eventually_holds_iff x (hx A (by simp))
    have hL := ih (fun B hB => hx B (by simp [hB]))
    filter_upwards [hA, hL] with y hyA hyL
    simp only [PolynomialSignDNF.clauseHolds_cons, hyA, hyL]

/-- All signs, including those of identically zero polynomials, are locally
constant wherever each nonzero defining polynomial has nonzero value. -/
theorem PolynomialSignDNF.eventually_mem_source_iff {n : ℕ}
    (F : PolynomialSignDNF n) (x : RealEuclidean n)
    (hx : ∀ L ∈ F.clauses, ∀ A ∈ L,
      A.polynomial = 0 ∨ MvPolynomial.eval (fun i => x i) A.polynomial ≠ 0) :
    ∀ᶠ y in 𝓝 x, y ∈ F.source ↔ x ∈ F.source := by
  classical
  have hclauses : ∀ᶠ y in 𝓝 x, ∀ L ∈ F.clauses,
      PolynomialSignDNF.clauseHolds L y ↔ PolynomialSignDNF.clauseHolds L x := by
    simpa only [List.mem_toFinset] using
      (Filter.eventually_all_finset F.clauses.toFinset).mpr
        (fun L hL => PolynomialSignDNF.eventually_clauseHolds_iff L x
          (hx L (by simpa only [List.mem_toFinset] using hL)))
  filter_upwards [hclauses] with y hy
  simp only [PolynomialSignDNF.source, Set.mem_ofPred_eq]
  exact exists_congr (fun L => and_congr_right (hy L))

/-- Every frontier point zeros a nonzero defining polynomial.
Constant-zero atoms are handled in the local-stability proof. -/
theorem PolynomialSignDNF.exists_nonzero_polynomial_zero_of_mem_frontier {n : ℕ}
    (F : PolynomialSignDNF n) {x : RealEuclidean n} (hx : x ∈ frontier F.source) :
    ∃ L ∈ F.clauses, ∃ A ∈ L,
      A.polynomial ≠ 0 ∧ MvPolynomial.eval (fun i => x i) A.polynomial = 0 := by
  classical
  by_contra hn
  push Not at hn
  have he : ∀ L ∈ F.clauses, ∀ A ∈ L,
      A.polynomial = 0 ∨ MvPolynomial.eval (fun i => x i) A.polynomial ≠ 0 := by
    intro L hL A hA
    by_cases hp : A.polynomial = 0
    · exact Or.inl hp
    · exact Or.inr (hn L hL A hA hp)
  have hstable := F.eventually_mem_source_iff x he
  rw [frontier_eq_inter_compl_interior] at hx
  by_cases hmem : x ∈ F.source
  · exact hx.1 ((mem_interior_iff_mem_nhds).mpr
      (hstable.mono (fun _ h => h.mpr hmem)))
  · exact hx.2 ((mem_interior_iff_mem_nhds).mpr
      (hstable.mono (fun _ h => fun hy => hmem (h.mp hy))))

/-- A null sign-formula set contains only roots of nonzero defining
polynomials. The result is a coefficient-free certificate, not an
algebraicity claim: algebraicity also requires rational coefficient preservation. -/
theorem PolynomialSignDNF.exists_nonzero_polynomial_zero_of_measure_eq_zero {n : ℕ}
    (F : PolynomialSignDNF n) (μ : MeasureTheory.Measure (RealEuclidean n))
    [MeasureTheory.Measure.IsOpenPosMeasure μ]
    (hnull : μ F.source = 0) {x : RealEuclidean n} (hx : x ∈ F.source) :
    ∃ L ∈ F.clauses, ∃ A ∈ L,
      A.polynomial ≠ 0 ∧ MvPolynomial.eval (fun i => x i) A.polynomial = 0 := by
  apply F.exists_nonzero_polynomial_zero_of_mem_frontier
  apply (mem_frontier_iff_notMem_interior hx).mpr
  intro hi
  have hp := MeasureTheory.Measure.measure_pos_of_nonempty_interior μ ⟨x, hi⟩
  rw [hnull] at hp
  exact lt_irrefl _ hp

end NLQCLean

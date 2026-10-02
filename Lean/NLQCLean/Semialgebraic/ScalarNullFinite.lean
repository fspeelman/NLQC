import NLQCLean.Arithmetic.PolynomialBoundary
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Roots

/-!
# Null semialgebraic subsets of the line are finite

A finite sign description is locally constant away from the zeros of its
nonzero atoms. A member of a null continuous pullback therefore zeros one of
finitely many nonzero atoms. In one variable each such atom has finitely many
roots, so a null scalar semialgebraic set is finite.
-/

namespace NLQCLean

open MeasureTheory Filter
open scoped Topology

/-- A member of a null continuous pullback zeros a nonzero atom of the
description. -/
theorem PolynomialSignDNF.exists_nonzero_atom_zero_of_pullback_null {n : ℕ}
    (F : PolynomialSignDNF n) {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (g : X → RealEuclidean n) (hg : Continuous g) (μ : Measure X)
    [μ.IsOpenPosMeasure] (hnull : μ (g ⁻¹' F.source) = 0) {x : X}
    (hx : g x ∈ F.source) :
    ∃ L ∈ F.clauses, ∃ A ∈ L,
      A.polynomial ≠ 0 ∧ MvPolynomial.eval (fun i => g x i) A.polynomial = 0 := by
  classical
  by_contra hn
  push Not at hn
  have he : ∀ L ∈ F.clauses, ∀ A ∈ L,
      A.polynomial = 0 ∨ MvPolynomial.eval (fun i => g x i) A.polynomial ≠ 0 := by
    intro L hL A hA
    by_cases hp : A.polynomial = 0
    · exact Or.inl hp
    · exact Or.inr (hn L hL A hA hp)
  have hstable := F.eventually_mem_source_iff (g x) he
  have hpull : ∀ᶠ y in 𝓝 x, g y ∈ F.source :=
    (hg.tendsto x).eventually (hstable.mono fun _ h => h.mpr hx)
  have hi : x ∈ interior (g ⁻¹' F.source) := mem_interior_iff_mem_nhds.mpr hpull
  have hp := μ.measure_pos_of_nonempty_interior ⟨x, hi⟩
  rw [hnull] at hp
  exact lt_irrefl _ hp

/-- A nonzero polynomial in one variable has finitely many real roots. -/
theorem finite_setOf_eval_const_eq_zero {p : MvPolynomial (Fin 1) ℝ} (hp : p ≠ 0) :
    {t : ℝ | MvPolynomial.eval (fun _ => t) p = 0}.Finite := by
  set q := MvPolynomial.uniqueAlgEquiv ℝ (Fin 1) p with hqdef
  have hq : q ≠ 0 := by
    intro h
    apply hp
    apply (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).injective
    rw [← hqdef, h, map_zero]
  refine (Polynomial.finite_setOfPred_isRoot hq).subset fun t ht => ?_
  simp only [Set.mem_ofPred_eq] at ht ⊢
  rw [Polynomial.IsRoot.def, Polynomial.eval, hqdef,
    MvPolynomial.eval₂_uniqueAlgEquiv (a := fun _ : Fin 1 => t)]
  exact ht

/-- **A null semialgebraic subset of the real line is finite.** The set is
presented through its one-coordinate Euclidean copy. -/
theorem finite_of_semialgebraic_scalar_null {T : Set ℝ}
    (hT : Semialgebraic {y : RealEuclidean 1 | y 0 ∈ T}) (hnull : volume T = 0) :
    T.Finite := by
  classical
  obtain ⟨F, hF⟩ := hT
  let g : ℝ → RealEuclidean 1 := fun t => WithLp.toLp 2 (fun _ => t)
  have hg : Continuous g := (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => continuous_id)
  have hpre : g ⁻¹' F.source = T := by
    rw [hF]
    rfl
  have hsub : T ⊆ ⋃ L ∈ F.clauses.toFinset, ⋃ A ∈ L.toFinset,
      {t : ℝ | A.polynomial ≠ 0 ∧ MvPolynomial.eval (fun _ => t) A.polynomial = 0} := by
    intro t ht
    have hgt : g t ∈ F.source := by
      rw [← Set.mem_preimage, hpre]
      exact ht
    obtain ⟨L, hL, A, hA, hA0, hAt⟩ := F.exists_nonzero_atom_zero_of_pullback_null g hg volume
      (by rw [hpre]; exact hnull) hgt
    simp only [Set.mem_iUnion, List.mem_toFinset]
    exact ⟨L, hL, A, hA, hA0, hAt⟩
  refine Set.Finite.subset ?_ hsub
  refine (F.clauses.toFinset.finite_toSet).biUnion fun L _ => ?_
  refine (L.toFinset.finite_toSet).biUnion fun A _ => ?_
  by_cases hA : A.polynomial = 0
  · simp [hA]
  · exact (finite_setOf_eval_const_eq_zero hA).subset fun t ht => ht.2

end NLQCLean

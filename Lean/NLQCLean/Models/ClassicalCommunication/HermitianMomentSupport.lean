import NLQCLean.Models.ClassicalCommunication.FiniteSupport
import NLQCLean.LinearAlgebra.AdjointDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Actual-outcome support for a Hermitian marginal and a real score

Equal trace removes one real affine coordinate from the Hermitian matrices;
the scalar score restores that coordinate. Caratheodory therefore selects at
most `card(input)² + 1` actual outcomes. This is a finite moment theorem, with
an explicit convex-hull hypothesis, rather than a quantum instrument bridge.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix Module

/-- Constant linear moments constrain the direction span of actual points. -/
theorem vectorSpan_range_le_ker_of_constant
    {E σ : Type*} [AddCommGroup E] [Module ℝ E]
    (f : σ → E) (L : E →ₗ[ℝ] ℝ) {c : ℝ} (hL : ∀ a, L (f a) = c) :
    vectorSpan ℝ (Set.range f) ≤ L.ker := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro z ⟨x, ⟨a, rfl⟩, y, ⟨b, rfl⟩, rfl⟩
  change L (f a - f b) = 0
  rw [map_sub, hL a, hL b, sub_self]

/-- Caratheodory with the sharper dimension of a constant-moment kernel. -/
theorem exists_finite_moment_support_of_constant
    {E σ : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (f : σ → E) (L : E →ₗ[ℝ] ℝ) {c : ℝ} (hL : ∀ a, L (f a) = c)
    {x : E} (hx : x ∈ convexHull ℝ (Set.range f)) :
    ∃ n : ℕ, n ≤ finrank ℝ L.ker + 1 ∧
      ∃ (select : Fin n → σ) (weight : Fin n → ℝ),
        (∀ j, 0 ≤ weight j) ∧ (∑ j, weight j) = 1 ∧
          (∑ j, weight j • f (select j)) = x := by
  classical
  let t := Caratheodory.minCardFinsetOfMemConvexHull hx
  have ht : (t : Set E) ⊆ Set.range f :=
    Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
  have hind : AffineIndependent ℝ ((↑) : t → E) :=
    Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
  have hconst (a : t) : L (a : E) = c := by
    obtain ⟨b, hb⟩ := ht a.property
    rw [← hb]
    exact hL b
  have hspan := vectorSpan_range_le_ker_of_constant ((↑) : t → E) L hconst
  have hcard : t.card ≤ finrank ℝ L.ker + 1 := by
    have h := hind.card_le_finrank_succ
    simpa only [Fintype.card_coe] using
      h.trans (Nat.add_le_add_right (Submodule.finrank_mono hspan) 1)
  have hm := Caratheodory.mem_minCardFinsetOfMemConvexHull hx
  change x ∈ convexHull ℝ (t : Set E) at hm
  rw [t.convexHull_eq] at hm
  obtain ⟨w, hw, hsum, hmean⟩ := hm
  let e : Fin t.card ≃ t := (Fintype.equivFinOfCardEq (Fintype.card_coe t)).symm
  have hvalues : ∀ j : Fin t.card, ∃ a : σ, f a = (e j : E) :=
    fun j => ht (e j).property
  choose select hselect using hvalues
  refine ⟨t.card, hcard, select, fun j => w (e j), ?_, ?_, ?_⟩
  · intro j
    exact hw _ (e j).property
  · calc
      ∑ j : Fin t.card, w (e j) = ∑ j : t, w j :=
        e.sum_comp (fun j : t => w (j : E))
      _ = ∑ j ∈ t, w j := Finset.sum_attach t w
      _ = 1 := hsum
  · rw [t.centerMass_eq_of_sum_1 id hsum] at hmean
    calc
      ∑ j : Fin t.card, w (e j) • f (select j) =
          ∑ j : Fin t.card, w (e j) • (e j : E) := by simp only [hselect]
      _ = ∑ j : t, w j • (j : E) :=
        e.sum_comp (fun j : t => w (j : E) • (j : E))
      _ = ∑ j ∈ t, w j • j := Finset.sum_attach t (fun j => w j • j)
      _ = x := hmean

/-- Real trace on the real vector space of Hermitian matrices. -/
def hermitianRealTrace (ι : Type*) [Fintype ι] [DecidableEq ι] :
    selfAdjoint (Matrix ι ι ℂ) →ₗ[ℝ] ℝ where
  toFun A := (A : Matrix ι ι ℂ).trace.re
  map_add' A B := by simp [Matrix.trace_add]
  map_smul' r A := by simp [Matrix.trace_smul]

section Hermitian

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance : FiniteDimensional ℝ (selfAdjoint (Matrix ι ι ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix ι ι ℂ)))

/-- Trace-zero Hermitian directions paired with a real score have dimension s². -/
theorem finrank_hermitian_trace_score_kernel :
    finrank ℝ ((hermitianRealTrace ι).comp
      (LinearMap.fst ℝ (selfAdjoint (Matrix ι ι ℂ)) ℝ)).ker = Fintype.card ι ^ 2 := by
  let L := (hermitianRealTrace ι).comp
    (LinearMap.fst ℝ (selfAdjoint (Matrix ι ι ℂ)) ℝ)
  have hL : L ≠ 0 := by
    intro hz
    have h := LinearMap.congr_fun hz ((1 : selfAdjoint (Matrix ι ι ℂ)), (0 : ℝ))
    have hcard : (Fintype.card ι : ℝ) = 0 := by
      simp [L, hermitianRealTrace, Matrix.trace_one] at h
    exact (Nat.cast_pos.mpr Fintype.card_pos : (0 : ℝ) < Fintype.card ι).ne' hcard
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hL
  rw [Module.finrank_prod, (finrank_adjoint_matrix_spaces ι).1,
    Module.finrank_self] at hdim
  change finrank ℝ L.ker = Fintype.card ι ^ 2
  omega

/-- At most s²+1 actual outcomes preserve a Hermitian marginal and real score. -/
theorem exists_hermitian_marginal_score_support
    (marginal : σ → selfAdjoint (Matrix ι ι ℂ)) (score : σ → ℝ)
    (M : selfAdjoint (Matrix ι ι ℂ)) (q : ℝ)
    (htrace : ∀ a, (marginal a : Matrix ι ι ℂ).trace.re = (M : Matrix ι ι ℂ).trace.re)
    (hmean : (M, q) ∈ convexHull ℝ (Set.range fun a => (marginal a, score a))) :
    ∃ n : ℕ, n ≤ Fintype.card ι ^ 2 + 1 ∧
      ∃ (select : Fin n → σ) (weight : Fin n → ℝ),
        (∀ j, 0 ≤ weight j) ∧ (∑ j, weight j) = 1 ∧
          (∑ j, weight j • marginal (select j)) = M ∧
          (∑ j, weight j * score (select j)) = q := by
  let L := (hermitianRealTrace ι).comp
    (LinearMap.fst ℝ (selfAdjoint (Matrix ι ι ℂ)) ℝ)
  have hconst : ∀ a, L (marginal a, score a) = (M : Matrix ι ι ℂ).trace.re := htrace
  obtain ⟨n, hn, select, weight, hweight, hsum, hm⟩ :=
    exists_finite_moment_support_of_constant (fun a => (marginal a, score a)) L
      hconst hmean
  refine ⟨n, ?_, select, weight, hweight, hsum, ?_, ?_⟩
  · simpa only [L, finrank_hermitian_trace_score_kernel] using hn
  · have h := congrArg Prod.fst hm
    simpa only [Prod.fst_sum, Prod.smul_fst] using h
  · have h := congrArg Prod.snd hm
    simpa only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul] using h

/-- The normalized-trace specialization preserves the input identity marginal. -/
theorem exists_normalized_hermitian_marginal_score_support
    (marginal : σ → selfAdjoint (Matrix ι ι ℂ)) (score : σ → ℝ) (q : ℝ)
    (htrace : ∀ a, (marginal a : Matrix ι ι ℂ).trace.re = Fintype.card ι)
    (hmean : ((1 : selfAdjoint (Matrix ι ι ℂ)), q) ∈
      convexHull ℝ (Set.range fun a => (marginal a, score a))) :
    ∃ n : ℕ, n ≤ Fintype.card ι ^ 2 + 1 ∧
      ∃ (select : Fin n → σ) (weight : Fin n → ℝ),
        (∀ j, 0 ≤ weight j) ∧ (∑ j, weight j) = 1 ∧
          (∑ j, weight j • marginal (select j)) = 1 ∧
          (∑ j, weight j * score (select j)) = q := by
  apply exists_hermitian_marginal_score_support marginal score 1 q ?_ hmean
  intro a
  simpa [Matrix.trace_one] using htrace a

end Hermitian

/-- The moment alphabet fits the uniform bound used for charged messages. -/
theorem moment_alphabet_le_twice_square (d r : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r) :
    (d * r) ^ 2 + 1 ≤ 2 * d ^ 2 * r ^ 2 := by
  have hprod : 1 ≤ d * r := by simpa using Nat.mul_le_mul hd hr
  have hsq : 1 ≤ (d * r) ^ 2 := by nlinarith
  nlinarith

/-- Any alphabet bounded by the actual-outcome support obeys the charged bound. -/
theorem alphabet_le_of_moment_support_bound (d r a : ℕ)
    (hd : 1 ≤ d) (hr : 1 ≤ r) (ha : a ≤ (d * r) ^ 2 + 1) :
    a ≤ 2 * d ^ 2 * r ^ 2 :=
  ha.trans (moment_alphabet_le_twice_square d r hd hr)

end NLQCLean.ClassicalCommunication

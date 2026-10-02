import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Basic.Real.Basic

/-!
# Finite support preserving a vector of moments

The support consists of attained values, so it can be used to select actual
outcomes.
-/

namespace NLQCLean.ClassicalCommunication

open Finset Module

/-- A point in the convex hull of actual moment values is a convex
combination of at most `finrank + 1` actual outcomes. -/
theorem exists_finite_moment_support {E σ : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (f : σ → E) {x : E}
    (hx : x ∈ convexHull ℝ (Set.range f)) :
    ∃ n : ℕ, n ≤ finrank ℝ E + 1 ∧
      ∃ (select : Fin n → σ) (weight : Fin n → ℝ),
        (∀ j, 0 ≤ weight j) ∧ (∑ j, weight j) = 1 ∧
          (∑ j, weight j • f (select j)) = x := by
  classical
  let t := Caratheodory.minCardFinsetOfMemConvexHull hx
  have ht : (t : Set E) ⊆ Set.range f :=
    Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
  have hind : AffineIndependent ℝ ((↑) : t → E) :=
    Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
  have hcard : t.card ≤ finrank ℝ E + 1 := by
    have h := hind.card_le_finrank_succ
    simpa only [Fintype.card_coe] using
      h.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
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

/-- The alphabet bounds imply the fifth-power charged footprint. -/
theorem charged_message_footprint_le (d r mA mB aA aB K : ℕ)
    (hmA : 1 ≤ mA) (hmB : 1 ≤ mB)
    (hK : r * mA * mB ≤ K)
    (haA : aA ≤ d ^ 2 * r ^ 2) (haB : aB ≤ d ^ 2 * r ^ 2) :
    r * (mA * aA) * (mB * aB) ≤ d ^ 4 * K ^ 5 := by
  have hrK : r ≤ K := by
    calc
      r ≤ r * mA := Nat.le_mul_of_pos_right _ hmA
      _ ≤ r * mA * mB := Nat.le_mul_of_pos_right _ hmB
      _ ≤ K := hK
  calc
    r * (mA * aA) * (mB * aB) = (r * mA * mB) * (aA * aB) := by ring
    _ ≤ K * ((d ^ 2 * r ^ 2) * (d ^ 2 * r ^ 2)) :=
      Nat.mul_le_mul hK (Nat.mul_le_mul haA haB)
    _ = d ^ 4 * r ^ 4 * K := by ring
    _ ≤ d ^ 4 * K ^ 4 * K :=
      Nat.mul_le_mul_right K (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hrK 4))
    _ = d ^ 4 * K ^ 5 := by ring

end NLQCLean.ClassicalCommunication

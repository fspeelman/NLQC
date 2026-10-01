/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.FormatParameters

/-!
# Basic closed polynomial conditions have a fixed sign format

Split each weak inequality into its zero and positive cases.
The resulting DNF has 2^w rows and e+w atoms per row, including zero counts.
-/

section

open Set

namespace NLQCLean

def nonnegativeSign (b : Bool) : PolynomialSign := if b then .positive else .zero

theorem exists_nonnegativeSign (t : ℝ) :
    (∃ b : Bool, (nonnegativeSign b).Holds t) ↔ 0 ≤ t := by
  simp only [Bool.exists_bool, nonnegativeSign, Bool.false_eq_true, if_false, if_true,
    PolynomialSign.Holds]
  constructor
  · rintro (h | h) <;> linarith
  · intro h
    by_cases hz : t = 0
    · exact Or.inl hz
    · exact Or.inr (lt_of_le_of_ne h (Ne.symm hz))

noncomputable def basicClosedSignDescription {n e w : ℕ}
    (eqs : Fin e → MvPolynomial (Fin n) ℝ) (ineqs : Fin w → MvPolynomial (Fin n) ℝ) :
    PolynomialSignDNF n := by
  classical
  exact ⟨(Finset.univ : Finset (Fin w → Bool)).toList.map fun σ =>
    List.ofFn (fun i => (⟨eqs i, .zero⟩ : PolynomialSignAtom n)) ++
    List.ofFn (fun j => (⟨ineqs j, nonnegativeSign (σ j)⟩ : PolynomialSignAtom n))⟩

theorem source_basicClosedSignDescription {n e w : ℕ}
    (eqs : Fin e → MvPolynomial (Fin n) ℝ) (ineqs : Fin w → MvPolynomial (Fin n) ℝ) :
    (basicClosedSignDescription eqs ineqs).source =
      {x | (∀ i, MvPolynomial.eval (fun j => x j) (eqs i) = 0) ∧
        (∀ i, 0 ≤ MvPolynomial.eval (fun j => x j) (ineqs i))} := by
  classical
  ext x
  constructor
  · rintro ⟨L, hL, hrow⟩
    obtain ⟨σ, _, rfl⟩ := List.mem_map.mp hL
    have h := (show PolynomialSignDNF.clauseHolds
      (List.ofFn (fun i => (⟨eqs i, .zero⟩ : PolynomialSignAtom n)) ++
       List.ofFn (fun j => (⟨ineqs j, nonnegativeSign (σ j)⟩ : PolynomialSignAtom n))) x from hrow)
    simp only [PolynomialSignDNF.clauseHolds, List.forall_mem_append,
      List.forall_mem_ofFn_iff, PolynomialSignAtom.Holds, PolynomialSign.Holds] at h
    obtain ⟨heq, hineq⟩ := h
    exact ⟨heq, fun i => (exists_nonnegativeSign _).mp ⟨σ i, hineq i⟩⟩
  · rintro ⟨heq, hineq⟩
    choose σ hσ using fun i => (exists_nonnegativeSign _).mpr (hineq i)
    refine ⟨_, List.mem_map.mpr ⟨σ, by simp, rfl⟩, ?_⟩
    simpa only [PolynomialSignDNF.clauseHolds, List.forall_mem_append,
      List.forall_mem_ofFn_iff, PolynomialSignAtom.Holds, PolynomialSign.Holds] using And.intro heq hσ

theorem basicClosedSignDescription_length {n e w : ℕ}
    (eqs : Fin e → MvPolynomial (Fin n) ℝ) (ineqs : Fin w → MvPolynomial (Fin n) ℝ) :
    (basicClosedSignDescription eqs ineqs).clauses.length = 2 ^ w := by
  classical
  simp [basicClosedSignDescription]

theorem basicClosedSignDescription_maxAtoms_le {n e w : ℕ}
    (eqs : Fin e → MvPolynomial (Fin n) ℝ) (ineqs : Fin w → MvPolynomial (Fin n) ℝ) :
    (basicClosedSignDescription eqs ineqs).maxAtoms ≤ e + w := by
  classical
  apply List.max_le_of_forall_le
  intro k hk
  obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hk
  obtain ⟨σ, _, rfl⟩ := List.mem_map.mp hL
  simp

theorem basicClosedSignDescription_hasFormat {n e w D : ℕ}
    (eqs : Fin e → MvPolynomial (Fin n) ℝ) (ineqs : Fin w → MvPolynomial (Fin n) ℝ)
    (heq : ∀ i, (eqs i).totalDegree ≤ D) (hineq : ∀ i, (ineqs i).totalDegree ≤ D) :
    (basicClosedSignDescription eqs ineqs).HasFormat ((e + w) * 2 ^ w) D := by
  classical
  constructor
  · rw [basicClosedSignDescription_length]
    simpa only [mul_comm] using
      Nat.mul_le_mul_left (2 ^ w) (basicClosedSignDescription_maxAtoms_le eqs ineqs)
  · intro L hL A hA
    obtain ⟨σ, _, rfl⟩ := List.mem_map.mp hL
    rcases List.mem_append.mp hA with hA | hA
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
      exact heq i
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
      exact hineq i

theorem PolynomialBasicClosedFormat.hasSemialgebraicFormat {n : ℕ}
    (F : PolynomialBasicClosedFormat n) : HasSemialgebraicFormat F.source (20 * 2 ^ 20) 100 := by
  refine ⟨basicClosedSignDescription F.equations F.inequalities,
    source_basicClosedSignDescription _ _, ?_⟩
  apply (basicClosedSignDescription_hasFormat _ _ F.equations_degree F.inequalities_degree).mono
  · exact Nat.mul_le_mul F.constraint_count
      (Nat.pow_le_pow_right (by norm_num) (by have := F.constraint_count; omega))
  · rfl

end NLQCLean
end

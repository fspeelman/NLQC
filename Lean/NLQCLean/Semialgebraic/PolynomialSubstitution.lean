/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.Projection

/-!
# Degree and format bounds under constant parameter specialization

Affine polynomial substitution does not increase total degree.
Fixing free parameter coordinates therefore preserves one description's
clause and degree caps. This is algebra, without any external input.
-/

section

open scoped BigOperators

namespace NLQCLean

theorem totalDegree_bind_le_of_affine {σ τ : Type*}
    (q : σ → MvPolynomial τ ℝ) (hq : ∀ i, (q i).totalDegree ≤ 1)
    (p : MvPolynomial σ ℝ) : (MvPolynomial.bind₁ q p).totalDegree ≤ p.totalDegree := by
  classical
  calc
    (MvPolynomial.bind₁ q p).totalDegree =
        (∑ d ∈ p.support, MvPolynomial.bind₁ q (MvPolynomial.monomial d (p.coeff d))).totalDegree := by
      rw [← map_sum, MvPolynomial.support_sum_monomial_coeff]
    _ ≤ p.totalDegree := by
      apply MvPolynomial.totalDegree_finsetSum_le
      intro d hd
      rw [MvPolynomial.bind₁_monomial]
      calc
        _ ≤ (MvPolynomial.C (p.coeff d)).totalDegree +
            (∏ i ∈ d.support, q i ^ d i).totalDegree := MvPolynomial.totalDegree_mul _ _
        _ = (∏ i ∈ d.support, q i ^ d i).totalDegree := by simp
        _ ≤ ∑ i ∈ d.support, (q i ^ d i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
        _ ≤ ∑ i ∈ d.support, d i := by
          apply Finset.sum_le_sum
          intro i _
          exact (MvPolynomial.totalDegree_pow _ _).trans
            (by simpa using Nat.mul_le_mul_left (d i) (hq i))
        _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd

namespace PolynomialSignDNF

variable {n m : ℕ}

@[simp] theorem length_pullback (F : PolynomialSignDNF n) (q : Fin n → MvPolynomial (Fin m) ℝ) :
    (F.pullback q).clauses.length = F.clauses.length := by simp [pullback]

@[simp] theorem maxAtoms_pullback (F : PolynomialSignDNF n) (q : Fin n → MvPolynomial (Fin m) ℝ) :
    (F.pullback q).maxAtoms = F.maxAtoms := by
  simp [maxAtoms, pullback, List.map_map, Function.comp_def]

theorem HasFormat.pullback_affine {F : PolynomialSignDNF n} {c D : ℕ}
    (hF : F.HasFormat c D) (q : Fin n → MvPolynomial (Fin m) ℝ)
    (hq : ∀ i, (q i).totalDegree ≤ 1) : (F.pullback q).HasFormat c D := by
  refine ⟨by simpa using hF.1, ?_⟩
  simp only [pullback, List.forall_mem_map]
  intro L hL A hA
  exact (totalDegree_bind_le_of_affine q hq A.polynomial).trans (hF.2 L hL A hA)

/-- Maximum total degree of the finite atom list, default zero. -/
noncomputable def maxDegree (F : PolynomialSignDNF n) : ℕ :=
  (F.clauses.flatten.map fun A => A.polynomial.totalDegree).foldr max 0

theorem hasFormat_self (F : PolynomialSignDNF n) :
    F.HasFormat (F.clauses.length * F.maxAtoms) F.maxDegree := by
  refine ⟨le_rfl, ?_⟩
  intro L hL A hA
  exact List.le_max_of_le (List.mem_map.mpr ⟨A, List.mem_flatten.mpr ⟨L, hL, hA⟩, rfl⟩) le_rfl

end PolynomialSignDNF

theorem Semialgebraic.exists_format {n : ℕ} {S : Set (RealEuclidean n)} (hS : Semialgebraic S) :
    ∃ c D : ℕ, HasSemialgebraicFormat S c D := by
  obtain ⟨F, rfl⟩ := hS
  exact ⟨_, _, F, rfl, F.hasFormat_self⟩

/-- Fix the first h coordinates at arbitrary real parameter values. -/
noncomputable def parameterSubstitution {h m : ℕ} (θ : RealEuclidean h) :
    Fin (h + m) → MvPolynomial (Fin m) ℝ :=
  Fin.append (fun i => MvPolynomial.C (θ i)) MvPolynomial.X

theorem totalDegree_parameterSubstitution {h m : ℕ} (θ : RealEuclidean h)
    (i : Fin (h + m)) : (parameterSubstitution θ i).totalDegree ≤ 1 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [parameterSubstitution]

theorem polynomialMap_parameterSubstitution {h m : ℕ} (θ : RealEuclidean h)
    (x : RealEuclidean m) : PolynomialSignDNF.polynomialMap (parameterSubstitution θ) x =
      euclideanPair θ x := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [parameterSubstitution, PolynomialSignDNF.polynomialMap]

/-- All parameter specializations use the very same diagram and degree caps. -/
theorem HasSemialgebraicFormat.specialize_parameters {h m c D : ℕ}
    {S : Set (RealEuclidean (h + m))} (hS : HasSemialgebraicFormat S c D)
    (θ : RealEuclidean h) :
    HasSemialgebraicFormat {x : RealEuclidean m | euclideanPair θ x ∈ S} c D := by
  obtain ⟨F, rfl, hF⟩ := hS
  refine ⟨F.pullback (parameterSubstitution θ), ?_,
    hF.pullback_affine _ (totalDegree_parameterSubstitution θ)⟩
  rw [PolynomialSignDNF.source_pullback]
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, polynomialMap_parameterSubstitution]

end NLQCLean
end

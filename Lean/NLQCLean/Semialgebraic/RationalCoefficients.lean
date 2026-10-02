/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Vendor.Sundog.PseudoRemainder
import Mathlib.Algebra.Polynomial.Eval.Subring

/-!
# Coefficient preservation in constructive polynomial elimination

The operations in the Sundog elimination algorithm use no division in the
parameter coefficient ring. This file proves that truncation, differentiation
and evenized pseudo-remainders preserve any coefficient subring. In particular,
rational parameter polynomials remain rational. These are closure lemmas, not
an additional quantifier-elimination premise.
-/

namespace NLQCLean

open Polynomial

/-- Univariate polynomials with coefficients in a specified subring. -/
noncomputable def polynomialSubring {R : Type*} [CommRing R] (S : Subring R) :
    Subring R[X] :=
  (Polynomial.mapRingHom S.subtype).range

theorem mem_polynomialSubring_iff {R : Type*} [CommRing R] (S : Subring R)
    (P : R[X]) : P ∈ polynomialSubring S ↔ ∀ i, P.coeff i ∈ S := by
  simp only [polynomialSubring, Polynomial.mem_map_range, Subring.range_subtype]

namespace polynomialSubring

variable {R : Type*} [CommRing R] {S : Subring R} {P Q : R[X]}

theorem coeff_mem (hP : P ∈ polynomialSubring S) (i : ℕ) : P.coeff i ∈ S :=
  (mem_polynomialSubring_iff S P).mp hP i

theorem leadingCoeff_mem (hP : P ∈ polynomialSubring S) : P.leadingCoeff ∈ S :=
  coeff_mem hP P.natDegree

theorem C_mem {c : R} (hc : c ∈ S) : C c ∈ polynomialSubring S := by
  refine (mem_polynomialSubring_iff S _).mpr ?_
  intro i
  rw [Polynomial.coeff_C]
  split_ifs <;> first | exact hc | exact S.zero_mem

theorem X_mem : (X : R[X]) ∈ polynomialSubring S := by
  refine (mem_polynomialSubring_iff S _).mpr ?_
  intro i
  rw [Polynomial.coeff_X]
  split_ifs <;> first | exact S.one_mem | exact S.zero_mem

theorem eraseLead_mem (hP : P ∈ polynomialSubring S) :
    P.eraseLead ∈ polynomialSubring S := by
  refine (mem_polynomialSubring_iff S _).mpr ?_
  intro i
  rw [Polynomial.eraseLead_coeff]
  split_ifs <;> first | exact S.zero_mem | exact coeff_mem hP i

theorem derivative_mem (hP : P ∈ polynomialSubring S) :
    P.derivative ∈ polynomialSubring S := by
  refine (mem_polynomialSubring_iff S _).mpr ?_
  intro i
  rw [Polynomial.coeff_derivative]
  exact S.mul_mem (coeff_mem hP (i + 1)) (by simpa only [Nat.cast_add, Nat.cast_one] using natCast_mem S (i + 1))

theorem pstep_mem (hP : P ∈ polynomialSubring S) (hQ : Q ∈ polynomialSubring S) :
    Sundog.TarskiQE.pstep P Q ∈ polynomialSubring S := by
  unfold Sundog.TarskiQE.pstep
  exact (polynomialSubring S).sub_mem
    ((polynomialSubring S).mul_mem (C_mem (leadingCoeff_mem hP)) hQ)
    ((polynomialSubring S).mul_mem (C_mem (leadingCoeff_mem hQ))
      ((polynomialSubring S).mul_mem ((polynomialSubring S).pow_mem X_mem _) hP))

theorem pseudoModExp_mem (hP : P ∈ polynomialSubring S)
    (hQ : Q ∈ polynomialSubring S) :
    (Sundog.TarskiQE.pseudoModExp P Q).2 ∈ polynomialSubring S := by
  classical
  suffices H : ∀ (N : ℕ) (Q : R[X]),
      (if Q = 0 then 0 else Q.natDegree + 1) ≤ N →
      Q ∈ polynomialSubring S →
      (Sundog.TarskiQE.pseudoModExp P Q).2 ∈ polynomialSubring S by
    exact H _ Q le_rfl hQ
  intro N
  induction N with
  | zero =>
    intro Q hN _
    have hQ0 : Q = 0 := by
      by_contra h
      rw [ite_eq_right h] at hN
      omega
    rw [Sundog.TarskiQE.pseudoModExp, dite_eq_left hQ0]
    exact (polynomialSubring S).zero_mem
  | succ N ih =>
    intro Q hN hQ
    rw [Sundog.TarskiQE.pseudoModExp]
    by_cases hQ0 : Q = 0
    · rw [dite_eq_left hQ0]
      exact (polynomialSubring S).zero_mem
    rw [dite_eq_right hQ0]
    by_cases hdeg : Q.natDegree < P.natDegree
    · rw [dite_eq_left hdeg]
      exact hQ
    rw [dite_eq_right hdeg]
    apply ih _ _ (pstep_mem hP hQ)
    rw [ite_eq_right hQ0] at hN
    have hstep := Sundog.TarskiQE.pstep_degree P Q (not_lt.mp hdeg)
    by_cases h0 : Sundog.TarskiQE.pstep P Q = 0
    · rw [ite_eq_left h0]
      omega
    · rw [ite_eq_right h0]
      rcases hstep with hzero | hlt
      · exact (h0 hzero).elim
      · omega

theorem emod_mem (hP : P ∈ polynomialSubring S) (hQ : Q ∈ polynomialSubring S) :
    Sundog.TarskiQE.emod P Q ∈ polynomialSubring S := by
  classical
  unfold Sundog.TarskiQE.emod
  split_ifs
  · exact pseudoModExp_mem hP hQ
  · exact (polynomialSubring S).mul_mem (C_mem (leadingCoeff_mem hP))
      (pseudoModExp_mem hP hQ)

end polynomialSubring

/-- Multivariate real polynomials obtained by extending rational coefficients. -/
noncomputable def rationalPolynomialSubring (σ : Type*) : Subring (MvPolynomial σ ℝ) :=
  (MvPolynomial.map (algebraMap ℚ ℝ)).range

theorem mem_rationalPolynomialSubring_iff {σ : Type*} (p : MvPolynomial σ ℝ) :
    p ∈ rationalPolynomialSubring σ ↔
      ∃ q : MvPolynomial σ ℚ, MvPolynomial.map (algebraMap ℚ ℝ) q = p := Iff.rfl

theorem rationalPolynomialSubring_coeff {σ : Type*} {p : MvPolynomial σ ℝ}
    (hp : p ∈ rationalPolynomialSubring σ) (i : σ →₀ ℕ) :
    p.coeff i ∈ (algebraMap ℚ ℝ).range := by
  obtain ⟨q, rfl⟩ := hp
  exact ⟨q.coeff i, MvPolynomial.coeff_map _ _ _ |>.symm⟩

theorem mem_rationalPolynomialSubring_of_coeff {σ : Type*} {p : MvPolynomial σ ℝ}
    (hp : ∀ i, p.coeff i ∈ (algebraMap ℚ ℝ).range) :
    p ∈ rationalPolynomialSubring σ := by
  apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
  intro c hc
  classical
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
  exact hp i

theorem rationalPolynomialSubring_rename {σ τ : Type*} {p : MvPolynomial σ ℝ}
    (hp : p ∈ rationalPolynomialSubring σ) (f : σ → τ) :
    MvPolynomial.rename f p ∈ rationalPolynomialSubring τ := by
  obtain ⟨q, rfl⟩ := hp
  exact ⟨MvPolynomial.rename f q, MvPolynomial.map_rename _ _ _⟩

theorem rationalPolynomialSubring_finSuccEquiv {n : ℕ}
    {p : MvPolynomial (Fin (n + 1)) ℝ}
    (hp : p ∈ rationalPolynomialSubring (Fin (n + 1))) :
    MvPolynomial.finSuccEquiv ℝ n p ∈ polynomialSubring (rationalPolynomialSubring (Fin n)) := by
  apply (mem_polynomialSubring_iff _ _).mpr
  intro i
  apply mem_rationalPolynomialSubring_of_coeff
  intro m
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  exact rationalPolynomialSubring_coeff hp _

theorem rationalPolynomialSubring_truncChain {n : ℕ}
    {P : Polynomial (MvPolynomial (Fin n) ℝ)}
    (hP : P ∈ polynomialSubring (rationalPolynomialSubring (Fin n))) :
    ∀ Q ∈ Sundog.TarskiQE.truncChain P,
      Q ∈ polynomialSubring (rationalPolynomialSubring (Fin n)) := by
  classical
  suffices H : ∀ (N : ℕ) (P : Polynomial (MvPolynomial (Fin n) ℝ)),
      P.support.card ≤ N → P ∈ polynomialSubring (rationalPolynomialSubring (Fin n)) →
      ∀ Q ∈ Sundog.TarskiQE.truncChain P,
        Q ∈ polynomialSubring (rationalPolynomialSubring (Fin n)) by
    exact H _ P le_rfl hP
  intro N
  induction N with
  | zero =>
    intro P hN _ Q hQ
    have h0 : P = 0 := by
      rw [← Polynomial.support_eq_empty, ← Finset.card_eq_zero]
      omega
    rw [Sundog.TarskiQE.truncChain, dite_eq_left h0, List.mem_singleton] at hQ
    subst Q
    exact (polynomialSubring _).zero_mem
  | succ N ih =>
    intro P hN hP Q hQ
    rw [Sundog.TarskiQE.truncChain] at hQ
    by_cases h0 : P = 0
    · rw [dite_eq_left h0, List.mem_singleton] at hQ
      subst Q
      exact (polynomialSubring _).zero_mem
    · rw [dite_eq_right h0, List.mem_cons] at hQ
      rcases hQ with rfl | hQ
      · exact hP
      · apply ih _ _ (polynomialSubring.eraseLead_mem hP) Q hQ
        have := Polynomial.eraseLead_support_card_lt h0
        omega

end NLQCLean

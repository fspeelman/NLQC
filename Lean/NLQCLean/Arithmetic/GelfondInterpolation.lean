import NLQCLean.Arithmetic.GelfondZeroEstimate
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Complex.Basic

/-!
# Confluent Hermite interpolation with explicit coefficient bounds

A complex polynomial of degree `< hT` whose derivatives of order `< T` at `0, …, h-1` are at
most `ε` has coefficients at most `ε · n^{n+1} (n^T h^n)^n`, `n = hT`. The data are the
image of the coefficients under an integer confluent Vandermonde matrix, which is
nonsingular (a polynomial of degree `< n` with zeros of order `T` at `h` points vanishes);
Cramer's rule and the Leibniz bound for the adjugate give the estimate.
-/

namespace NLQCLean.Gelfond

open Polynomial
open scoped Matrix

/-- The interpolation constant `n^{n+1} (n^T h^n)^n`, `n = hT`. -/
def interpConst (h T : ℕ) : ℕ := (h * T) ^ (h * T + 1) * ((h * T) ^ T * h ^ (h * T)) ^ (h * T)

/-- The integer confluent Vandermonde matrix, rows `(s, t)` and columns the coefficients. -/
def confluentVandermonde (h T : ℕ) : Matrix (Fin (h * T)) (Fin (h * T)) ℤ := fun i k =>
  let st := finProdFinEquiv.symm i
  ((k : ℕ).descFactorial (st.2 : ℕ) * (st.1 : ℕ) ^ ((k : ℕ) - st.2) : ℕ)

/-- Zeros of order `T` at `0, …, h-1` force a polynomial of degree `< hT` to vanish. -/
theorem eq_zero_of_hermite_zero {p : ℂ[X]} {h T : ℕ} (hdeg : p.natDegree < h * T)
    (hzero : ∀ s < h, ∀ t < T, (derivative^[t] p).eval (s : ℂ) = 0) : p = 0 := by
  classical
  by_contra hp
  have hdvd : ∀ s ∈ Finset.range h, (X - C (s : ℂ)) ^ T ∣ p := by
    intro s hs
    rcases Nat.eq_zero_or_pos T with hT | hT
    · subst hT; simp
    have hlt : T - 1 < p.rootMultiplicity (s : ℂ) :=
      (lt_rootMultiplicity_iff_isRoot_iterate_derivative hp).mpr fun m hm =>
        hzero s (Finset.mem_range.mp hs) m (by omega)
    exact (pow_dvd_pow _ (by omega)).trans (pow_rootMultiplicity_dvd p _)
  have hprod : ∏ s ∈ Finset.range h, (X - C (s : ℂ)) ^ T ∣ p := by
    refine Finset.prod_dvd_of_coprime ?_ hdvd
    intro a _ b _ hab
    exact ((pairwise_coprime_X_sub_C (s := fun n : ℕ => (n : ℂ))
      (Nat.cast_injective (R := ℂ)) hab).pow)
  have hne : ∏ s ∈ Finset.range h, (X - C (s : ℂ)) ^ T ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun s _ => pow_ne_zero _ (X_sub_C_ne_zero _)
  have hdeg' := natDegree_le_of_dvd hprod hp
  rw [natDegree_prod _ _ (fun s _ => pow_ne_zero _ (X_sub_C_ne_zero _))] at hdeg'
  simp only [natDegree_pow, natDegree_X_sub_C, mul_one, Finset.sum_const, Finset.card_range,
    smul_eq_mul] at hdeg'
  omega

theorem confluentVandermonde_mulVec {p : ℂ[X]} {h T : ℕ} (hdeg : p.natDegree < h * T)
    (i : Fin (h * T)) :
    ((confluentVandermonde h T).map (Int.cast : ℤ → ℂ) *ᵥ (fun k : Fin (h * T) => p.coeff k)) i =
      (derivative^[(finProdFinEquiv.symm i).2] p).eval
        (((finProdFinEquiv.symm i).1 : ℕ) : ℂ) := by
  rw [eval_iterate_derivative_eq_sum p _ _ hdeg, Matrix.mulVec, dotProduct, Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [confluentVandermonde, Matrix.map_apply]
  push_cast
  ring

theorem confluentVandermonde_det_ne_zero (h T : ℕ) : (confluentVandermonde h T).det ≠ 0 := by
  classical
  intro hdet
  have hdetC : ((confluentVandermonde h T).map (Int.cast : ℤ → ℂ)).det = 0 := by
    rw [show (confluentVandermonde h T).map (Int.cast : ℤ → ℂ) =
      (Int.castRingHom ℂ).mapMatrix (confluentVandermonde h T) from rfl, ← RingHom.map_det,
      hdet, map_zero]
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetC
  set p : ℂ[X] := ∑ k : Fin (h * T), C (w k) * X ^ (k : ℕ) with hp
  have hcoeff : ∀ k : Fin (h * T), p.coeff k = w k := by
    intro k
    rw [hp, finsetSum_coeff, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      rw [coeff_C_mul_X_pow, ite_eq_right (fun h => hb (Fin.ext h.symm))]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hdeg : p.natDegree < h * T := by
    rcases Nat.eq_zero_or_pos (h * T) with h0 | hpos
    · exact absurd (funext fun k => (Fin.elim0 (h0 ▸ k) : w k = 0)) hw0
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := h * T - 1) fun k _ => ?_) ?_
    · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
    · omega
  have hp0 : p = 0 := by
    refine eq_zero_of_hermite_zero hdeg fun s hs t ht => ?_
    have := congrFun hw (finProdFinEquiv (⟨s, hs⟩, ⟨t, ht⟩))
    have hwv : (fun k : Fin (h * T) => p.coeff k) = w := funext hcoeff
    rw [← hwv, confluentVandermonde_mulVec hdeg] at this
    simpa using this
  exact hw0 (funext fun k => by rw [← hcoeff k, hp0]; simp)

theorem abs_confluentVandermonde_le (h T : ℕ) (_hT : 1 ≤ T) (i k : Fin (h * T)) :
    |confluentVandermonde h T i k| ≤ ((h * T) ^ T * h ^ (h * T) : ℕ) := by
  have hn : 1 ≤ h * T := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
    (Nat.pos_of_ne_zero (fun h0 => by have := k.isLt; omega)))
  simp only [confluentVandermonde]
  rw [abs_of_nonneg (by positivity)]
  have h1 : (k : ℕ).descFactorial ((finProdFinEquiv.symm i).2 : ℕ) ≤ (h * T) ^ T :=
    (Nat.descFactorial_le_pow _ _).trans ((Nat.pow_le_pow_left k.isLt.le _).trans
      (Nat.pow_le_pow_right hn (finProdFinEquiv.symm i).2.isLt.le))
  have h2 : (((finProdFinEquiv.symm i).1 : ℕ) : ℕ) ^ ((k : ℕ) - ((finProdFinEquiv.symm i).2 : ℕ)) ≤
      h ^ (h * T) := by
    rcases Nat.eq_zero_or_pos ((k : ℕ) - ((finProdFinEquiv.symm i).2 : ℕ)) with h0 | hpos
    · rw [h0, pow_zero]; exact Nat.one_le_pow _ _ (by
        have := (finProdFinEquiv.symm i).1.isLt; omega)
    · exact (Nat.pow_le_pow_left (finProdFinEquiv.symm i).1.isLt.le _).trans
        (Nat.pow_le_pow_right (by have := (finProdFinEquiv.symm i).1.isLt; omega) (by omega))
  exact_mod_cast Nat.mul_le_mul h1 h2

theorem abs_adjugate_confluentVandermonde_le (h T : ℕ) (hT : 1 ≤ T) (k i : Fin (h * T)) :
    |(confluentVandermonde h T).adjugate k i| ≤
      ((h * T) ^ (h * T) * ((h * T) ^ T * h ^ (h * T)) ^ (h * T) : ℕ) := by
  classical
  set M : ℕ := (h * T) ^ T * h ^ (h * T) with hM
  have hM1 : 1 ≤ M := by
    rw [hM]
    have hnpos : 0 < h * T := lt_of_le_of_lt (Nat.zero_le _) k.isLt
    have hhpos : 0 < h := Nat.pos_of_ne_zero (by rintro rfl; simp at hnpos)
    exact Nat.mul_pos (pow_pos hnpos _) (pow_pos hhpos _)
  rw [Matrix.adjugate_apply]
  have hentry : ∀ a b, AbsoluteValue.abs
      (((confluentVandermonde h T).updateRow i (Pi.single k 1)) a b) ≤ (M : ℤ) := by
    intro a b
    by_cases ha : a = i
    · subst ha
      simp only [Matrix.updateRow_self, Pi.single_apply, AbsoluteValue.abs_apply]
      split_ifs <;> simp; exact_mod_cast hM1
    · rw [Matrix.updateRow_ne ha]
      exact abs_confluentVandermonde_le h T hT a b
  have hdet := Matrix.det_le hentry
  simp only [Fintype.card_fin, AbsoluteValue.abs_apply, nsmul_eq_mul] at hdet
  refine hdet.trans ?_
  have hfac : ((h * T).factorial : ℤ) ≤ ((h * T) ^ (h * T) : ℕ) := by
    exact_mod_cast Nat.factorial_le_pow _
  push_cast at hfac ⊢
  exact mul_le_mul_of_nonneg_right hfac (by positivity)

/-- **Interpolation bound.** -/
theorem norm_coeff_le_of_hermite_data {p : ℂ[X]} {h T : ℕ} (hh : 1 ≤ h) (hT : 1 ≤ T)
    (hdeg : p.natDegree < h * T) {ε : ℝ}
    (hdata : ∀ s < h, ∀ t < T, ‖(derivative^[t] p).eval (s : ℂ)‖ ≤ ε) (k : ℕ) :
    ‖p.coeff k‖ ≤ ε * interpConst h T := by
  classical
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hdata 0 hh 0 hT)
  by_cases hk : h * T ≤ k
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]; positivity
  replace hk := not_le.mp hk
  set n := h * T with hn
  set V := confluentVandermonde h T
  set Vc := V.map (Int.cast : ℤ → ℂ) with hVc
  set v : Fin n → ℂ := fun k => p.coeff k
  have hd : ∀ i, ‖(Vc *ᵥ v) i‖ ≤ ε := fun i => by
    rw [confluentVandermonde_mulVec hdeg]
    exact hdata _ (finProdFinEquiv.symm i).1.isLt _ (finProdFinEquiv.symm i).2.isLt
  have hkey : Vc.det • v = Vc.adjugate *ᵥ (Vc *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hdetC : Vc.det = (V.det : ℂ) := by
    rw [hVc, show V.map (Int.cast : ℤ → ℂ) = (Int.castRingHom ℂ).mapMatrix V from rfl,
      ← RingHom.map_det]; rfl
  have hdet1 : (1 : ℝ) ≤ ‖Vc.det‖ := by
    rw [hdetC, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs (confluentVandermonde_det_ne_zero h T)
  have hadj : ∀ i, Vc.adjugate ⟨k, hk⟩ i = (V.adjugate ⟨k, hk⟩ i : ℂ) := by
    intro i
    rw [hVc, show V.map (Int.cast : ℤ → ℂ) = (Int.castRingHom ℂ).mapMatrix V from rfl,
      ← RingHom.map_adjugate]; rfl
  have hcomp := congrFun hkey ⟨k, hk⟩
  simp only [Pi.smul_apply, smul_eq_mul] at hcomp
  have hbound : ‖(Vc.adjugate *ᵥ (Vc *ᵥ v)) ⟨k, hk⟩‖ ≤
      n * (((n ^ n * (n ^ T * h ^ n) ^ n : ℕ) : ℝ) * ε) := by
    rw [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖Vc.adjugate ⟨k, hk⟩ i * (Vc *ᵥ v) i‖
        ≤ ∑ _i : Fin n, ((n ^ n * (n ^ T * h ^ n) ^ n : ℕ) : ℝ) * ε := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul, hadj, Complex.norm_intCast]
          refine mul_le_mul ?_ (hd i) (norm_nonneg _) (by positivity)
          exact_mod_cast abs_adjugate_confluentVandermonde_le h T hT ⟨k, hk⟩ i
      _ = n * (((n ^ n * (n ^ T * h ^ n) ^ n : ℕ) : ℝ) * ε) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hvk : ‖v ⟨k, hk⟩‖ ≤ n * (((n ^ n * (n ^ T * h ^ n) ^ n : ℕ) : ℝ) * ε) := by
    calc ‖v ⟨k, hk⟩‖ = 1 * ‖v ⟨k, hk⟩‖ := (one_mul _).symm
      _ ≤ ‖Vc.det‖ * ‖v ⟨k, hk⟩‖ := mul_le_mul_of_nonneg_right hdet1 (norm_nonneg _)
      _ = ‖(Vc.adjugate *ᵥ (Vc *ᵥ v)) ⟨k, hk⟩‖ := by rw [← norm_mul, hcomp]
      _ ≤ _ := hbound
  refine hvk.trans (le_of_eq ?_)
  simp only [interpConst, ← hn]
  push_cast
  ring

end NLQCLean.Gelfond

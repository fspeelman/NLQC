import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Bezout
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# A Liouville inequality over the Gaussian integers

Let `G ∈ ℤ[i][X]` be irreducible of degree `g ≥ 1` with a root `β₀`, and let `Q ∈ ℤ[i][X]`
have degree at most `q` and coefficients at most `A`. If
`|Q(β₀)| ((q+1)A)^{g-1} M(G)^q < 1` then `G ∣ Q`: the resultant `Res(G, Q)` is a Gaussian
integer of absolute value `< 1`, so it vanishes; by Gauss's lemma `G` stays irreducible over
`ℚ(i)`, hence divides `Q` there and in `ℤ[i][X]`.
-/

namespace NLQCLean.Gelfond

open Polynomial GaussianInt

/-- `ℚ(i)[X]` is a principal ideal ring (the Euclidean structure, with the instance path
made explicit). -/
noncomputable instance : IsPrincipalIdealRing (FractionRing GaussianInt)[X] :=
  @EuclideanDomain.instIsPrincipalIdealRing (FractionRing GaussianInt)[X] _

/-- A nonzero Gaussian integer has absolute value at least one. -/
theorem one_le_norm_toComplex {z : GaussianInt} (hz : z ≠ 0) : 1 ≤ ‖(z : ℂ)‖ := by
  have h1 : (1 : ℝ) ≤ Complex.normSq (z : ℂ) := by
    rw [← intCast_real_norm]
    exact_mod_cast (norm_pos.mpr hz)
  have h2 : Complex.normSq (z : ℂ) = ‖(z : ℂ)‖ ^ 2 := Complex.normSq_eq_norm_sq _
  nlinarith [_root_.norm_nonneg (z : ℂ)]

/-- Crude bound for the value of a polynomial. -/
theorem norm_eval_le_of_coeff_le {p : ℂ[X]} {q : ℕ} {A : ℝ} (hq : p.natDegree ≤ q)
    (hA : ∀ k, ‖p.coeff k‖ ≤ A) (β : ℂ) :
    ‖p.eval β‖ ≤ (q + 1) * A * max 1 ‖β‖ ^ q := by
  have hA0 : 0 ≤ A := (_root_.norm_nonneg _).trans (hA 0)
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hq)]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ Finset.range (q + 1), ‖p.coeff k * β ^ k‖
      ≤ ∑ _k ∈ Finset.range (q + 1), A * max 1 ‖β‖ ^ q := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [norm_mul, norm_pow]
        refine mul_le_mul (hA k) ?_ (by positivity) hA0
        calc ‖β‖ ^ k ≤ max 1 ‖β‖ ^ k := pow_le_pow_left₀ (_root_.norm_nonneg _) (le_max_right _ _) _
          _ ≤ max 1 ‖β‖ ^ q := pow_le_pow_right₀ (le_max_left _ _)
              (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    _ = (q + 1) * A * max 1 ‖β‖ ^ q := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

theorem norm_prod_map_le (s : Multiset ℂ) (f : ℂ → ℂ) (B : ℂ → ℝ) (hB : ∀ β, ‖f β‖ ≤ B β) :
    ‖(s.map f).prod‖ ≤ (s.map B).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, norm_mul]
    have hB0 : ∀ β, 0 ≤ B β := fun β => (_root_.norm_nonneg _).trans (hB β)
    exact mul_le_mul (hB a) ih (_root_.norm_nonneg _) (hB0 a)

/-- **Liouville over `ℤ[i]`.** -/
theorem dvd_of_norm_eval_root_small {G Q : GaussianInt[X]} (hG : Irreducible G)
    (hdeg : 0 < G.natDegree) {β₀ : ℂ} (hβ : (G.map toComplex).eval β₀ = 0) {q : ℕ} {A : ℝ}
    (hq : Q.natDegree ≤ q) (hA : ∀ k, ‖(Q.coeff k : ℂ)‖ ≤ A)
    (hsmall : ‖(Q.map toComplex).eval β₀‖ *
      (((q + 1) * A) ^ (G.natDegree - 1) * (G.map toComplex).mahlerMeasure ^ q) < 1) :
    G ∣ Q := by
  classical
  by_cases hQ0 : Q = 0
  · rw [hQ0]; exact dvd_zero _
  have hA0 : 0 ≤ A := (_root_.norm_nonneg _).trans (hA 0)
  set Gc := G.map toComplex with hGc
  set Qc := Q.map toComplex with hQc
  have hGdeg : Gc.natDegree = G.natDegree := natDegree_map_eq_of_injective toComplex_injective _
  have hQdeg : Qc.natDegree = Q.natDegree := natDegree_map_eq_of_injective toComplex_injective _
  have hG0 : G ≠ 0 := hG.ne_zero
  have hGc0 : Gc ≠ 0 := (Polynomial.map_ne_zero_iff toComplex_injective).mpr hG0
  have hsplit : Gc.Splits := IsAlgClosed.splits Gc
  -- the resultant over `ℂ`
  set R := resultant G Q with hR
  have hRc : (R : ℂ) = Gc.leadingCoeff ^ Q.natDegree * (Gc.roots.map Qc.eval).prod := by
    have h1 := resultant_map_map G Q G.natDegree Q.natDegree toComplex
    have h2 := resultant_eq_prod_eval Gc Qc Q.natDegree hQdeg.le hsplit
    rw [hGdeg] at h2
    rw [hR]
    change toComplex (resultant G Q G.natDegree Q.natDegree) = _
    rw [← h1]
    exact h2
  have hroot : β₀ ∈ Gc.roots := (mem_roots hGc0).mpr hβ
  have hcard : Gc.roots.card = G.natDegree := by rw [← hGdeg]; exact hsplit.natDegree_eq_card_roots.symm
  have hlc1 : 1 ≤ ‖Gc.leadingCoeff‖ := by
    rw [hGc, leadingCoeff_map_of_injective toComplex_injective]
    exact one_le_norm_toComplex (leadingCoeff_ne_zero.mpr hG0)
  have hQcA : ∀ k, ‖Qc.coeff k‖ ≤ A := fun k => by rw [hQc, coeff_map]; exact hA k
  have hQval : ∀ β, ‖Qc.eval β‖ ≤ (q + 1) * A * max 1 ‖β‖ ^ q :=
    norm_eval_le_of_coeff_le (hQdeg.le.trans hq) hQcA
  have hRsmall : ‖(R : ℂ)‖ < 1 := by
    have hprodle : ‖((Gc.roots.erase β₀).map Qc.eval).prod‖ ≤
        ((Gc.roots.erase β₀).map fun β => (q + 1) * A * max 1 ‖β‖ ^ q).prod :=
      norm_prod_map_le _ _ _ hQval
    have h2 : ((Gc.roots.erase β₀).map fun β => (q + 1) * A * max 1 ‖β‖ ^ q).prod =
        ((q + 1) * A) ^ (G.natDegree - 1) *
          ((Gc.roots.erase β₀).map fun β => max 1 ‖β‖ ^ q).prod := by
      rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
        Multiset.card_erase_of_mem hroot, hcard]
      rfl
    have hmax0 : 0 ≤ ((Gc.roots.erase β₀).map fun β => max 1 ‖β‖ ^ q).prod :=
      Multiset.prod_nonneg fun x hx => by
        obtain ⟨β, -, rfl⟩ := Multiset.mem_map.mp hx
        positivity
    have h3 : ((Gc.roots.erase β₀).map fun β => max 1 ‖β‖ ^ q).prod ≤
        (Gc.roots.map fun β => max 1 ‖β‖).prod ^ q := by
      rw [← Multiset.prod_map_pow, ← Multiset.prod_map_erase hroot]
      exact le_mul_of_one_le_left hmax0 (one_le_pow₀ (le_max_left _ _))
    have hM := mahlerMeasure_eq_leadingCoeff_mul_prod_roots Gc
    have hlcpow : ‖Gc.leadingCoeff‖ ^ Q.natDegree ≤ ‖Gc.leadingCoeff‖ ^ q :=
      pow_le_pow_right₀ hlc1 hq
    have hqA : 0 ≤ ((q + 1 : ℝ) * A) ^ (G.natDegree - 1) := by positivity
    calc ‖(R : ℂ)‖
        = ‖Gc.leadingCoeff‖ ^ Q.natDegree *
            (‖Qc.eval β₀‖ * ‖((Gc.roots.erase β₀).map Qc.eval).prod‖) := by
          rw [hRc, norm_mul, norm_pow, ← Multiset.prod_map_erase hroot, norm_mul]
      _ ≤ ‖Gc.leadingCoeff‖ ^ q * (‖Qc.eval β₀‖ * (((q + 1) * A) ^ (G.natDegree - 1) *
            (Gc.roots.map fun β => max 1 ‖β‖).prod ^ q)) := by
          refine mul_le_mul hlcpow (mul_le_mul_of_nonneg_left ?_ (_root_.norm_nonneg _))
            (by positivity) (by positivity)
          exact hprodle.trans (h2 ▸ mul_le_mul_of_nonneg_left h3 hqA)
      _ = ‖Qc.eval β₀‖ * (((q + 1) * A) ^ (G.natDegree - 1) *
            (‖Gc.leadingCoeff‖ * (Gc.roots.map fun β => max 1 ‖β‖).prod) ^ q) := by ring
      _ = ‖Qc.eval β₀‖ * (((q + 1) * A) ^ (G.natDegree - 1) * Gc.mahlerMeasure ^ q) := by
          rw [hM]
      _ < 1 := hsmall
  have hR0 : R = 0 := by
    by_contra hne
    exact absurd (one_le_norm_toComplex hne) (not_le.mpr hRsmall)
  -- over the fraction field
  have hinj : Function.Injective (algebraMap GaussianInt (FractionRing GaussianInt)) := IsFractionRing.injective _ _
  have hresK : resultant (G.map (algebraMap GaussianInt (FractionRing GaussianInt))) (Q.map (algebraMap GaussianInt (FractionRing GaussianInt))) = 0 := by
    have := resultant_map_map G Q G.natDegree Q.natDegree (algebraMap GaussianInt (FractionRing GaussianInt))
    rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj] at *
    rw [this, ← hR, hR0, map_zero]
  have hprim := hG.isPrimitive hdeg.ne'
  have hGK : Irreducible (G.map (algebraMap GaussianInt (FractionRing GaussianInt))) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map).mp hG
  have hncop := ((resultant_eq_zero_iff).mp hresK).2
  have hdvdK : G.map (algebraMap GaussianInt (FractionRing GaussianInt)) ∣ Q.map (algebraMap GaussianInt (FractionRing GaussianInt)) := by
    by_contra hnd
    exact hncop ((hGK.coprime_iff_not_dvd).mpr hnd)
  exact hprim.dvd_of_fraction_map_dvd_fraction_map hdvdK

end NLQCLean.Gelfond

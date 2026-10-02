import NLQCLean.Arithmetic.GelfondInterpolation
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# An approximate Schwarz lemma for polynomials

Let `F ∈ ℂ[X]` have derivatives of order `< T` at `0, …, h-1` of size at most `ε` and be at
most `M` on `|w| = 8h`. Write `F = Π S + H` with `Π = ∏_{s<h} (X - s)^T`. The remainder `H`
is bounded by interpolation, `S` by the maximum principle on `|w| ≤ 8h`, and Cauchy's
estimate on `|z - s₀| = 1` bounds every derivative of `Π S` at `s₀` by
`t! (M + max|H|) / 7^{hT}`.
-/

namespace NLQCLean.Gelfond

open Polynomial Metric

theorem iteratedDeriv_eval (p : ℂ[X]) (t : ℕ) :
    iteratedDeriv t (fun z => p.eval z) = fun z => (derivative^[t] p).eval z := by
  induction t generalizing p with
  | zero => simp
  | succ t ih =>
    rw [iteratedDeriv_succ', show deriv (fun z => p.eval z) = fun z => p.derivative.eval z from
      funext fun z => Polynomial.deriv p, ih, Function.iterate_succ_apply]

theorem iterate_derivative_add' (p q : ℂ[X]) (t : ℕ) :
    derivative^[t] (p + q) = derivative^[t] p + derivative^[t] q := by
  induction t generalizing p q with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      Function.iterate_succ_apply, derivative_add, ih]

/-- The product `∏_{s<h} (X - s)^T`. -/
noncomputable def nodePoly (h T : ℕ) : ℂ[X] := ∏ s ∈ Finset.range h, (X - C (s : ℂ)) ^ T

theorem nodePoly_monic (h T : ℕ) : (nodePoly h T).Monic :=
  monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _

theorem natDegree_nodePoly (h T : ℕ) : (nodePoly h T).natDegree = h * T := by
  rw [nodePoly, natDegree_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _]
  simp only [natDegree_pow, natDegree_X_sub_C, mul_one, Finset.sum_const, Finset.card_range,
    smul_eq_mul]

theorem dvd_nodePoly {h T s : ℕ} (hs : s < h) : (X - C (s : ℂ)) ^ T ∣ nodePoly h T :=
  Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hs)

theorem norm_eval_nodePoly_ge {h T : ℕ} {w : ℂ} (hw : ‖w‖ = 8 * h) :
    ((7 : ℝ) * h) ^ (h * T) ≤ ‖(nodePoly h T).eval w‖ := by
  rw [nodePoly, eval_prod, norm_prod]
  simp only [eval_pow, eval_sub, eval_X, eval_C, norm_pow]
  calc ((7 : ℝ) * h) ^ (h * T) = ∏ _s ∈ Finset.range h, ((7 : ℝ) * h) ^ T := by
        rw [Finset.prod_const, Finset.card_range, ← pow_mul, mul_comm T h]
    _ ≤ ∏ s ∈ Finset.range h, ‖w - s‖ ^ T := by
        refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun s hs => ?_
        refine pow_le_pow_left₀ (by positivity) ?_ _
        have hs' : (s : ℝ) ≤ h := by exact_mod_cast (Finset.mem_range.mp hs).le
        have := norm_sub_norm_le w (s : ℂ)
        rw [hw, Complex.norm_natCast] at this
        linarith

theorem norm_eval_nodePoly_le {h T s₀ : ℕ} (hs₀ : s₀ < h) {z : ℂ} (hz : ‖z - s₀‖ ≤ 1) :
    ‖(nodePoly h T).eval z‖ ≤ (h : ℝ) ^ (h * T) := by
  rw [nodePoly, eval_prod, norm_prod]
  simp only [eval_pow, eval_sub, eval_X, eval_C, norm_pow]
  calc ∏ s ∈ Finset.range h, ‖z - s‖ ^ T ≤ ∏ _s ∈ Finset.range h, (h : ℝ) ^ T := by
        refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun s hs => ?_
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
        have hs' := Finset.mem_range.mp hs
        calc ‖z - s‖ = ‖(z - s₀) + ((s₀ : ℂ) - s)‖ := by ring_nf
          _ ≤ ‖z - s₀‖ + ‖(s₀ : ℂ) - s‖ := norm_add_le _ _
          _ ≤ 1 + (h - 1 : ℝ) := by
              refine add_le_add hz ?_
              rw [show ((s₀ : ℂ) - s) = (((s₀ : ℤ) - s : ℤ) : ℂ) by push_cast; ring,
                Complex.norm_intCast]
              have : |((s₀ : ℤ) - s : ℤ)| ≤ (h : ℤ) - 1 := by
                rw [abs_le]; constructor <;> omega
              exact_mod_cast this
          _ = h := by ring
    _ = (h : ℝ) ^ (h * T) := by rw [Finset.prod_const, Finset.card_range, ← pow_mul, mul_comm T h]

/-- **Approximate Schwarz lemma.** -/
theorem norm_iterate_derivative_le_schwarz (F : ℂ[X]) {h T : ℕ} (hh : 1 ≤ h) (hT : 1 ≤ T)
    {ε M : ℝ} (hε : ∀ s < h, ∀ t < T, ‖(derivative^[t] F).eval (s : ℂ)‖ ≤ ε)
    (hM : ∀ w : ℂ, ‖w‖ = 8 * h → ‖F.eval w‖ ≤ M) {s₀ : ℕ} (hs₀ : s₀ < h) (t : ℕ) :
    ‖(derivative^[t] F).eval (s₀ : ℂ)‖ ≤
      t.factorial * (M + ((h * T : ℕ) : ℝ) * (ε * interpConst h T) * (8 * h) ^ (h * T)) /
        7 ^ (h * T) + ((h * T : ℕ) : ℝ) * (ε * interpConst h T) *
          (((h * T : ℕ) : ℝ) ^ t * h ^ (h * T)) := by
  set n := h * T with hn
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  set P := nodePoly h T
  set H := F %ₘ P
  set S := F /ₘ P
  have hsplit : F = P * S + H := by rw [add_comm]; exact (modByMonic_add_div F P).symm
  have hP1 : P ≠ 1 := fun h1 => by
    have := natDegree_nodePoly h T
    rw [show nodePoly h T = P from rfl, h1, natDegree_one] at this
    omega
  have hHdeg : H.natDegree < n := by
    have := natDegree_modByMonic_lt F (nodePoly_monic h T) hP1
    rwa [natDegree_nodePoly] at this
  -- data of the remainder
  have hHdata : ∀ s < h, ∀ t < T, ‖(derivative^[t] H).eval (s : ℂ)‖ ≤ ε := by
    intro s hs t ht
    have hPS : (derivative^[t] (P * S)).eval (s : ℂ) = 0 :=
      eval_iterate_derivative_eq_zero_of_dvd ((dvd_nodePoly hs).trans (dvd_mul_right _ _)) ht
    have : derivative^[t] H = derivative^[t] F - derivative^[t] (P * S) := by
      conv_rhs => rw [hsplit]
      rw [iterate_derivative_add']; ring
    rw [this, eval_sub, hPS, sub_zero]
    exact hε s hs t ht
  set cH := ε * interpConst h T with hcH
  have hHcoeff : ∀ k, ‖H.coeff k‖ ≤ cH := norm_coeff_le_of_hermite_data hh hT hHdeg hHdata
  have hcH0 : 0 ≤ cH := (norm_nonneg _).trans (hHcoeff 0)
  have h8 : (1 : ℝ) ≤ 8 * h := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  -- size of the remainder on `|w| ≤ 8h`
  have hHval : ∀ w : ℂ, ‖w‖ ≤ 8 * h → ‖H.eval w‖ ≤ n * cH * (8 * h) ^ n := by
    intro w hw
    rw [eval_eq_sum_range' hHdeg]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ Finset.range n, ‖H.coeff k * w ^ k‖
        ≤ ∑ _k ∈ Finset.range n, cH * (8 * (h : ℝ)) ^ n := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [norm_mul, norm_pow]
          refine mul_le_mul (hHcoeff k) ?_ (by positivity) hcH0
          exact (pow_le_pow_left₀ (norm_nonneg _) hw k).trans
            (pow_le_pow_right₀ h8 (Finset.mem_range.mp hk).le)
      _ = n * cH * (8 * h) ^ n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  set B := (M + n * cH * (8 * h) ^ n) / ((7 : ℝ) * h) ^ n with hB
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  -- `S` on the circle and inside
  have hSsphere : ∀ w ∈ sphere (0 : ℂ) (8 * h), ‖S.eval w‖ ≤ B := by
    intro w hw
    rw [mem_sphere_zero_iff_norm] at hw
    have hPw := norm_eval_nodePoly_ge (T := T) hw
    have hPpos : 0 < ‖P.eval w‖ := lt_of_lt_of_le (by positivity) hPw
    have hFw : F.eval w = P.eval w * S.eval w + H.eval w := by
      conv_lhs => rw [hsplit]
      rw [eval_add, eval_mul]
    have hS : ‖S.eval w‖ * ‖P.eval w‖ ≤ M + n * cH * (8 * h) ^ n := by
      calc ‖S.eval w‖ * ‖P.eval w‖ = ‖F.eval w - H.eval w‖ := by
            rw [hFw, add_sub_cancel_right, norm_mul, mul_comm]
        _ ≤ ‖F.eval w‖ + ‖H.eval w‖ := norm_sub_le _ _
        _ ≤ M + n * cH * (8 * h) ^ n := add_le_add (hM w hw) (hHval w hw.le)
    rw [hB, le_div_iff₀ (by positivity)]
    calc ‖S.eval w‖ * ((7 : ℝ) * h) ^ n ≤ ‖S.eval w‖ * ‖P.eval w‖ :=
          mul_le_mul_of_nonneg_left hPw (norm_nonneg _)
      _ ≤ _ := hS
  have hSin : ∀ z : ℂ, ‖z‖ ≤ 8 * h → ‖S.eval z‖ ≤ B := by
    intro z hz
    have hr : (8 : ℝ) * h ≠ 0 := by positivity
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) (8 * h))
      isBounded_ball (S.differentiable.diffContOnCl) (fun w hw => ?_) ?_
    · rw [frontier_ball (0 : ℂ) hr] at hw; exact hSsphere w hw
    · rw [closure_ball (0 : ℂ) hr, mem_closedBall_zero_iff]; exact hz
  -- Cauchy estimate for `P S` at `s₀`
  have hPS : ‖(derivative^[t] (P * S)).eval (s₀ : ℂ)‖ ≤
      t.factorial * (M + n * cH * (8 * h) ^ n) / 7 ^ n := by
    have hC : ∀ z ∈ sphere (s₀ : ℂ) 1, ‖(P * S).eval z‖ ≤ (h : ℝ) ^ n * B := by
      intro z hz
      rw [mem_sphere_iff_norm] at hz
      rw [eval_mul, norm_mul]
      have hzn : ‖z‖ ≤ 8 * h := by
        calc ‖z‖ = ‖(z - s₀) + s₀‖ := by ring_nf
          _ ≤ ‖z - s₀‖ + ‖(s₀ : ℂ)‖ := norm_add_le _ _
          _ ≤ 1 + h := by
              rw [hz, Complex.norm_natCast]
              have : (s₀ : ℝ) ≤ h := by exact_mod_cast hs₀.le
              linarith
          _ ≤ 8 * h := by
              have : (1 : ℝ) ≤ h := by exact_mod_cast hh
              linarith
      exact mul_le_mul (norm_eval_nodePoly_le hs₀ hz.le) (hSin z hzn) (norm_nonneg _)
        (by positivity)
    have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le t one_pos
      ((P * S).differentiable.diffContOnCl) hC
    rw [iteratedDeriv_eval, one_pow, div_one] at this
    refine this.trans (le_of_eq ?_)
    rw [hB, mul_pow]
    field_simp
    ring
  -- derivatives of the remainder at `s₀`
  have hHs₀ : ‖(derivative^[t] H).eval (s₀ : ℂ)‖ ≤ n * cH * (n ^ t * h ^ n) := by
    rw [eval_iterate_derivative_eq_sum H t _ hHdeg]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ Finset.range n, ‖H.coeff k * ((k.descFactorial t : ℂ) * (s₀ : ℂ) ^ (k - t))‖
        ≤ ∑ _k ∈ Finset.range n, cH * ((n : ℝ) ^ t * (h : ℝ) ^ n) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' := Finset.mem_range.mp hk
          rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
          refine mul_le_mul (hHcoeff k) (mul_le_mul ?_ ?_ (by positivity) (by positivity))
            (by positivity) hcH0
          · exact_mod_cast (Nat.descFactorial_le_pow k t).trans (Nat.pow_le_pow_left hk'.le t)
          · have : (s₀ : ℝ) ≤ h := by exact_mod_cast hs₀.le
            calc (s₀ : ℝ) ^ (k - t) ≤ (h : ℝ) ^ (k - t) := pow_le_pow_left₀ (by positivity) this _
              _ ≤ (h : ℝ) ^ n := pow_le_pow_right₀ (by exact_mod_cast hh) (by omega)
      _ = n * cH * (n ^ t * h ^ n) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hdecomp : (derivative^[t] F).eval (s₀ : ℂ) =
      (derivative^[t] (P * S)).eval (s₀ : ℂ) + (derivative^[t] H).eval (s₀ : ℂ) := by
    conv_lhs => rw [hsplit]
    rw [iterate_derivative_add', eval_add]
  rw [hdecomp]
  refine (norm_add_le _ _).trans (add_le_add hPS ?_)
  exact_mod_cast hHs₀

end NLQCLean.Gelfond

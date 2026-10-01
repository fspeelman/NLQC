import NLQCLean.Bounds.ResourceArithmetic
import NLQCLean.Bounds.CodimensionArithmetic

/-!
# Arithmetic of the universal PVM resource lower bound

The PVM codimension d⁴−3d²+2 dominates the unitary codimension
d⁴−4d²+3, so the unchanged square-root arithmetic applies. No geometric
hypothesis is introduced.
-/

namespace NLQCLean

theorem pvm_resource_lower_of_one_le_haar_rhs {d K : ℕ} (hd : 2 ≤ d) {C e : ℝ}
    (hC : 0 < C) (he : 0 < e) (he1 : e ≤ 1)
    (h : 1 ≤ Real.exp (C * (d : ℝ) ^ 2 * (K : ℝ) ^ 2) *
      e ^ ((pvmCodimension d : ℝ) / 2)) :
    Real.sqrt (3 / (32 * C)) * (d : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K := by
  have hL : 0 ≤ Real.log (1 / e) := Real.log_nonneg ((one_le_div₀ he).mpr he1)
  have hlog := log_bound_of_one_le_haar_rhs he h
  have hcod : (unitaryCodimension d : ℝ) ≤ pvmCodimension d := by
    exact_mod_cast unitaryCodimension_le_pvmCodimension hd
  refine resource_lower_of_log_bound hd hC (Nat.cast_nonneg K) hL ?_
  have hmono := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcod
    (by norm_num : (0 : ℝ) ≤ 2)) hL
  exact hmono.trans hlog

end NLQCLean

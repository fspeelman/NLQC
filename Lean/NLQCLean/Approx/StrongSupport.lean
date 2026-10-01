import NLQCLean.LinearAlgebra.FlatSupport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Support sizes for near-SWAP witnesses

The frozen environment ceiling and uncontrolled-direction count used by the
near-SWAP freezing and tube arguments, with their elementary bounds.
-/

namespace NLQCLean

/-- The frozen environment support `s = ⌈K/q⌉`, by natural ceiling division. -/
def frozenSupport (d K : ℕ) : ℕ := (K + flatSupportCount d - 1) / flatSupportCount d

theorem flatSupportCount_mul_frozenSupport_bounds {d : ℕ} (hd : 0 < d) (K : ℕ) :
    K ≤ flatSupportCount d * frozenSupport d K ∧
      flatSupportCount d * frozenSupport d K + 1 ≤ K + flatSupportCount d := by
  have hq := flatSupportCount_pos hd
  have h1 := Nat.div_add_mod (K + flatSupportCount d - 1) (flatSupportCount d)
  have h2 := Nat.mod_lt (K + flatSupportCount d - 1) hq
  unfold frozenSupport
  generalize flatSupportCount d * ((K + flatSupportCount d - 1) / flatSupportCount d) = t at h1 ⊢
  omega

theorem le_flatSupportCount_mul_frozenSupport {d : ℕ} (hd : 0 < d) (K : ℕ) :
    K ≤ flatSupportCount d * frozenSupport d K :=
  (flatSupportCount_mul_frozenSupport_bounds hd K).1

theorem one_le_frozenSupport {d K : ℕ} (hd : 0 < d) (hK : 1 ≤ K) : 1 ≤ frozenSupport d K := by
  have h := le_flatSupportCount_mul_frozenSupport hd K
  rcases Nat.eq_zero_or_pos (frozenSupport d K) with h0 | h0
  · rw [h0, Nat.mul_zero] at h
    omega
  · exact h0

/-- `s ≤ 4K/D` in the form `D s ≤ 4K`, once `D ≤ 2K`. -/
theorem sq_mul_frozenSupport_le {d K : ℕ} (hd : 0 < d) (hK : d ^ 2 ≤ 2 * K) :
    d ^ 2 * frozenSupport d K ≤ 4 * K := by
  have hb := (flatSupportCount_mul_frozenSupport_bounds hd K).2
  have hq2 := two_mul_flatSupportCount_le d
  have hsq := Nat.mul_le_mul_right (frozenSupport d K) (sq_le_two_mul_flatSupportCount d)
  rw [Nat.mul_assoc] at hsq
  generalize flatSupportCount d * frozenSupport d K = t at hb hsq
  generalize d ^ 2 * frozenSupport d K = u at hsq ⊢
  omega

theorem frozenSupport_le {d K : ℕ} (hd : 2 ≤ d) (hK : d ^ 2 ≤ 2 * K) : frozenSupport d K ≤ K := by
  have h := sq_mul_frozenSupport_le (by omega) hK
  have h4 : 4 ≤ d ^ 2 := by nlinarith
  have hm := Nat.mul_le_mul_right (frozenSupport d K) h4
  omega

example : frozenSupport 2 1 = 1 := by decide
example : frozenSupport 2 2 = 1 := by decide
example : frozenSupport 2 4 = 2 := by decide
example : frozenSupport 3 5 = 1 := by decide
example : frozenSupport 3 6 = 2 := by decide

/-- The number of uncontrolled directions `b = 4D − 3 + 4D⌊D/64⌋`. -/
def strongUncontrolledRank (d : ℕ) : ℕ := (4 * d ^ 2 - 3) + 4 * d ^ 2 * (d ^ 2 / 64)

/-- `b ≤ 7N/8`, including `D = 4` and every `D < 64`. -/
theorem eight_mul_strongUncontrolledRank_le {d : ℕ} (hd : 2 ≤ d) :
    8 * strongUncontrolledRank d ≤ 7 * d ^ 4 := by
  have h4 : d ^ 4 = d ^ 2 * d ^ 2 := by ring
  unfold strongUncontrolledRank
  rw [h4]
  have hD : 4 ≤ d ^ 2 := by nlinarith
  generalize d ^ 2 = D at hD ⊢
  have ht : 64 * (D / 64) ≤ D := Nat.mul_div_le D 64
  generalize D / 64 = t at ht ⊢
  have hsub : 4 * D - 3 + 3 = 4 * D := by omega
  generalize 4 * D - 3 = w at hsub ⊢
  have hDt : 64 * (D * t) ≤ D * D := by nlinarith
  have hquad : 13 * D * 4 ≤ 13 * D * D := Nat.mul_le_mul_left _ hD
  nlinarith

theorem strongUncontrolledRank_le {d : ℕ} (hd : 2 ≤ d) : strongUncontrolledRank d ≤ d ^ 4 := by
  have h := eight_mul_strongUncontrolledRank_le hd
  omega

end NLQCLean

import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Basic

/-!
# Flat spectral support counts

Elementary arithmetic for the number `⌈d²/2⌉` of flat Schmidt indices used
by the product top-mass estimate.
-/

namespace NLQCLean

/-- `q = ⌈D/2⌉`, the number of selected flat Schmidt indices. -/
def flatSupportCount (d : ℕ) : ℕ := (d ^ 2 + 1) / 2

theorem flatSupportCount_pos {d : ℕ} (hd : 0 < d) : 0 < flatSupportCount d := by
  have h : 1 ≤ d ^ 2 := Nat.one_le_pow _ _ hd
  unfold flatSupportCount
  omega

theorem sq_le_two_mul_flatSupportCount (d : ℕ) : d ^ 2 ≤ 2 * flatSupportCount d := by
  unfold flatSupportCount
  omega

theorem two_mul_flatSupportCount_le (d : ℕ) : 2 * flatSupportCount d ≤ d ^ 2 + 1 := by
  unfold flatSupportCount
  omega

end NLQCLean

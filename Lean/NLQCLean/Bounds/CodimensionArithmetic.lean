import Lean.Elab.Tactic.Omega
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Unitary and PVM codimension arithmetic

The transverse codimensions and their elementary comparisons, separated from
the witness geometry and Haar estimates that use them.
-/

namespace NLQCLean

/-- The real-transverse dimension deficit in the unitary argument, prior to real division by two. -/
def unitaryCodimension (d : ℕ) : ℕ := d ^ 4 - (4 * d ^ 2 - 3)

theorem unitaryCodimension_eq {d : ℕ} (hd : 2 ≤ d) :
    unitaryCodimension d = d ^ 4 - 4 * d ^ 2 + 3 := by
  have hs : 4 ≤ d ^ 2 := by nlinarith
  have hp : d ^ 4 = d ^ 2 * d ^ 2 := by ring
  have h4 : 4 * d ^ 2 ≤ d ^ 4 := by nlinarith
  unfold unitaryCodimension
  omega

theorem unitaryCodimension_cast {d : ℕ} (hd : 2 ≤ d) :
    (unitaryCodimension d : ℝ) = (d : ℝ) ^ 4 - 4 * (d : ℝ) ^ 2 + 3 := by
  rw [unitaryCodimension_eq hd]
  have hs : 4 ≤ d ^ 2 := by nlinarith
  have hp : d ^ 4 = d ^ 2 * d ^ 2 := by ring
  have h4 : 4 * d ^ 2 ≤ d ^ 4 := by nlinarith
  rw [Nat.cast_add, Nat.cast_sub h4]
  push_cast
  ring

/-- The unitary codimension is uniformly at least three sixteenths of the group dimension. -/
theorem unitaryCodimension_lower {d : ℕ} (hd : 2 ≤ d) :
    (3 / 16 : ℝ) * (d : ℝ) ^ 4 ≤ unitaryCodimension d := by
  rw [unitaryCodimension_cast hd]
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (0 : ℝ) ≤ (d : ℝ) ^ 2 - 4 := by nlinarith
  have h2 : (0 : ℝ) ≤ 13 * (d : ℝ) ^ 2 - 12 := by nlinarith
  nlinarith [mul_nonneg h1 h2]

/-- The transverse real codimension in the ordered rank-one PVM argument. -/
def pvmCodimension (d : ℕ) : ℕ := d ^ 4 - (3 * d ^ 2 - 2)

theorem pvmCodimension_eq {d : ℕ} (hd : 2 ≤ d) :
    pvmCodimension d = d ^ 4 - 3 * d ^ 2 + 2 := by
  have hs : 4 ≤ d ^ 2 := by nlinarith
  have hp : d ^ 4 = d ^ 2 * d ^ 2 := by ring
  have h3 : 3 * d ^ 2 ≤ d ^ 4 := by nlinarith
  unfold pvmCodimension
  omega

theorem unitaryCodimension_le_pvmCodimension {d : ℕ} (hd : 2 ≤ d) :
    unitaryCodimension d ≤ pvmCodimension d := by
  have hs : 4 ≤ d ^ 2 := by nlinarith
  unfold unitaryCodimension pvmCodimension
  apply Nat.sub_le_sub_left
  generalize d ^ 2 = x at *
  omega

/-- The unitary exponent is at least three thirty-seconds of the group dimension. -/
theorem unitaryCodimension_half_lower {d : ℕ} (hd : 2 ≤ d) :
    (3 / 32 : ℝ) * (d : ℝ) ^ 4 ≤ (unitaryCodimension d : ℝ) / 2 := by
  have h := unitaryCodimension_lower hd
  linarith

/-- The PVM exponent is at least three thirty-seconds of the group dimension. -/
theorem pvmCodimension_half_lower {d : ℕ} (hd : 2 ≤ d) :
    (3 / 32 : ℝ) * (d : ℝ) ^ 4 ≤ (pvmCodimension d : ℝ) / 2 := by
  have h1 := unitaryCodimension_lower hd
  have h2 : (unitaryCodimension d : ℝ) ≤ pvmCodimension d := by
    exact_mod_cast unitaryCodimension_le_pvmCodimension hd
  linarith

end NLQCLean

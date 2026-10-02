import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.Bounds.FiniteClassicalHaar

/-!
# Stronger universal unitary bound for finite-shape classical protocols

finite pure and common-map mixed unitary score universality transfers
to the charged universal score class at `4 d⁴ K⁵`. The existing stronger
charged universal resource theorem, proved using the near-SWAP restricted
Haar estimate and its positive patch mass, then gives a fourth-power dimension
factor in the logarithm bound. No full-group strong Haar estimate, stronger
almost-every rate or PVM improvement is asserted.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix

/-- The stronger charged lower bound cancels four powers of the dimension
after squaring the fifth-power budget. -/
theorem log_le_fourth_tenth_power_of_finite_strong_charged_lower_bound
    {c L : ℝ} {d K : ℕ} (hc : 0 < c) (hd : 0 < d) (hL : 0 ≤ L)
    (hbound : c * (d : ℝ) ^ 2 * Real.sqrt L ≤ 4 * (d : ℝ) ^ 4 * (K : ℝ) ^ 5) :
    L ≤ (16 / c ^ 2) * (d : ℝ) ^ 4 * (K : ℝ) ^ 10 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsquare := pow_le_pow_left₀ (by positivity) hbound 2
  rw [mul_pow, mul_pow, Real.sq_sqrt hL] at hsquare
  have hcancel : c ^ 2 * L ≤ 16 * (d : ℝ) ^ 4 * (K : ℝ) ^ 10 := by
    apply (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < (d : ℝ) ^ 4)).mp
    calc
      (d : ℝ) ^ 4 * (c ^ 2 * L) = c ^ 2 * ((d : ℝ) ^ 2) ^ 2 * L := by ring
      _ ≤ (4 * (d : ℝ) ^ 4 * (K : ℝ) ^ 5) ^ 2 := hsquare
      _ = (d : ℝ) ^ 4 * (16 * (d : ℝ) ^ 4 * (K : ℝ) ^ 10) := by ring
  have hdiv : L ≤ (16 * (d : ℝ) ^ 4 * (K : ℝ) ^ 10) / c ^ 2 := by
    apply (le_div_iff₀ (by positivity : 0 < c ^ 2)).mpr
    simpa only [mul_comm L (c ^ 2)] using hcancel
  convert hdiv using 1
  ring

/-- One constant precedes all dimensions, quantum budgets and errors.
Universality allows a different finite-shape protocol for each target.
The stronger rate applies to unitary score universality only. -/
theorem exists_finite_classical_strong_unitary_universal_log_constant_of_imageVolumeBound
    (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ((∀ U, U ∈ finitePureScoreReachable d K ε) →
          Real.log (1 / ε) ≤ C * (d : ℝ) ^ 4 * (K : ℝ) ^ 10) ∧
        ((∀ U, U ∈ finiteMixedScoreReachable d K ε) →
          Real.log (1 / ε) ≤ C * (d : ℝ) ^ 4 * (K : ℝ) ^ 10) := by
  obtain ⟨c, hc, hbound⟩ := exists_strongUniversalResourceBound_of_imageVolumeBound hGeom
  refine ⟨16 / c ^ 2, by positivity, ?_⟩
  intro d K hd _hK ε hε hεhalf
  have hd0 : 0 < d := by omega
  have hL : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((one_le_div₀ hε).mpr (by linarith))
  have hcharged := (hbound d (4 * d ^ 4 * K ^ 5) hd ε hε hεhalf).1
  have htransfer (hreach : ∀ U, U ∈ pureReachable d (4 * d ^ 4 * K ^ 5) ε) :
      Real.log (1 / ε) ≤ (16 / c ^ 2) * (d : ℝ) ^ 4 * (K : ℝ) ^ 10 := by
    apply log_le_fourth_tenth_power_of_finite_strong_charged_lower_bound hc hd0 hL
    have h := hcharged hreach
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h
  exact ⟨fun hu => htransfer (fun U =>
      finitePureScoreReachable_subset_pureReachable hd0 ε (hu U)),
    fun hu => htransfer (fun U =>
      finiteMixedScoreReachable_subset_pureReachable hd0 ε (hu U))⟩

/-- The improved finite-shape unitary universal bound. Compression is proved, and the
restricted near-SWAP argument remains inside the charged universal theorem. -/
theorem exists_finite_classical_strong_unitary_universal_log_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ((∀ U, U ∈ finitePureScoreReachable d K ε) →
          Real.log (1 / ε) ≤ C * (d : ℝ) ^ 4 * (K : ℝ) ^ 10) ∧
        ((∀ U, U ∈ finiteMixedScoreReachable d K ε) →
          Real.log (1 / ε) ≤ C * (d : ℝ) ^ 4 * (K : ℝ) ^ 10) :=
  exists_finite_classical_strong_unitary_universal_log_constant_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

end NLQCLean.ClassicalCommunication

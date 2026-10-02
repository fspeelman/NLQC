import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.Models.ClassicalCommunication.FiniteReachability
import NLQCLean.Bounds.Quantitative

/-!
# Haar and universal bounds for finite-shape classical protocols

The twelve-system finite protocol classes enter the charged score
classes at footprint `d⁴ * K⁵`. Their Haar bounds are outer-measure bounds:
no measurability of these new protocol classes is assumed or asserted. The
unitary and PVM conclusions retain their different score codimensions. No
diamond or joint-TV error preservation is used, and arbitrary-register
reindexing, standard-Borel outcomes and shared randomness are outside this
finite-shape statement.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix MeasureTheory
open scoped ENNReal

/-- The fifth-power charged budget satisfies both hypotheses of the
existing full-group Haar theorem without a new resource floor assumption. -/
theorem finiteClassical_charged_budget_admissible {d K : ℕ}
    (hd : 2 ≤ d) (hK : 1 ≤ K) :
    1 ≤ d ^ 4 * K ^ 5 ∧ (d : ℝ) ^ 2 / 4 ≤ (d ^ 4 * K ^ 5 : ℕ) := by
  have hd0 : 0 < d := by omega
  have hK0 : 0 < K := by omega
  have hone : 0 < d ^ 4 * K ^ 5 := by positivity
  have hpow : d ^ 2 ≤ d ^ 4 := Nat.pow_le_pow_right hd0 (by decide)
  have hmul : d ^ 4 ≤ d ^ 4 * K ^ 5 := Nat.le_mul_of_pos_right _ (by positivity)
  have hfull : d ^ 2 ≤ d ^ 4 * K ^ 5 := hpow.trans hmul
  have hreal : (d : ℝ) ^ 2 ≤ (d ^ 4 * K ^ 5 : ℕ) := by exact_mod_cast hfull
  exact ⟨by omega, by nlinarith [sq_nonneg (d : ℝ)]⟩

/-- Squaring `d⁴ K⁵` leaves the Haar coefficient unchanged. -/
theorem finiteClassical_haar_exponent_eq (C : ℝ) (d K : ℕ) :
    C * (d : ℝ) ^ 2 * ((d ^ 4 * K ^ 5 : ℕ) : ℝ) ^ 2 =
      C * (d : ℝ) ^ 10 * (K : ℝ) ^ 10 := by
  push_cast
  ring

/-- Full-group unitary score bounds for pure and common-map mixed
finite-shape protocols. The constant is the charged Haar constant. -/
theorem exists_finite_classical_unitary_haar_constant_of_imageVolumeBound
    (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        (unitaryHaar (Fin d × Fin d)).toOuterMeasure (finitePureScoreReachable d K ε) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 10 * (K : ℝ) ^ 10) *
            ε ^ ((unitaryCodimension d : ℝ) / 2))) ∧
        (unitaryHaar (Fin d × Fin d)).toOuterMeasure (finiteMixedScoreReachable d K ε) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 10 * (K : ℝ) ^ 10) *
            ε ^ ((unitaryCodimension d : ℝ) / 2))) := by
  obtain ⟨C, hC, hbound⟩ := exists_haar_fraction_constant_of_imageVolumeBound hGeom
  refine ⟨C, hC, ?_⟩
  intro d K hd hK ε hε hεhalf
  obtain ⟨hone, hquarter⟩ := finiteClassical_charged_budget_admissible hd hK
  have h := (hbound d (d ^ 4 * K ^ 5) hd hone hquarter ε hε hεhalf).2.2.1
  rw [finiteClassical_haar_exponent_eq] at h
  exact ⟨(measure_mono (finitePureScoreReachable_subset_pureReachable
      (by omega : 0 < d) ε)).trans h,
    (measure_mono (finiteMixedScoreReachable_subset_pureReachable
      (by omega : 0 < d) ε)).trans h⟩

/-- Full-group joint-correct-label PVM score bounds for the same finite
classes. This is the PVM score, not a substituted unitary or marginal score. -/
theorem exists_finite_classical_pvm_haar_constant_of_imageVolumeBound
    (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        (unitaryHaar (Fin d × Fin d)).toOuterMeasure (finitePurePVMScoreReachable d K ε) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 10 * (K : ℝ) ^ 10) *
            ε ^ ((pvmCodimension d : ℝ) / 2))) ∧
        (unitaryHaar (Fin d × Fin d)).toOuterMeasure (finiteMixedPVMScoreReachable d K ε) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 10 * (K : ℝ) ^ 10) *
            ε ^ ((pvmCodimension d : ℝ) / 2))) := by
  obtain ⟨C, hC, hbound⟩ := exists_pvm_haar_fraction_constant_of_imageVolumeBound hGeom
  refine ⟨C, hC, ?_⟩
  intro d K hd hK ε hε hεhalf
  obtain ⟨hone, hquarter⟩ := finiteClassical_charged_budget_admissible hd hK
  have h := (hbound d (d ^ 4 * K ^ 5) hd hone hquarter ε hε hεhalf).2.2.1
  rw [finiteClassical_haar_exponent_eq] at h
  exact ⟨(measure_mono (finitePurePVMScoreReachable_subset_purePVMReachable
      (by omega : 0 < d) ε)).trans h,
    (measure_mono (finiteMixedPVMScoreReachable_subset_purePVMReachable
      (by omega : 0 < d) ε)).trans h⟩

/-- The finite-shape unitary outer-measure conclusion. -/
theorem exists_finite_classical_unitary_haar_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        (unitaryHaar (Fin d × Fin d)).toOuterMeasure (finitePureScoreReachable d K ε) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 10 * (K : ℝ) ^ 10) *
            ε ^ ((unitaryCodimension d : ℝ) / 2))) ∧
        (unitaryHaar (Fin d × Fin d)).toOuterMeasure (finiteMixedScoreReachable d K ε) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 10 * (K : ℝ) ^ 10) *
            ε ^ ((unitaryCodimension d : ℝ) / 2))) :=
  exists_finite_classical_unitary_haar_constant_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

/-- The PVM outer-measure conclusion has the same three arguments and its
original PVM codimension. No measurability of the finite class is assumed. -/
theorem exists_finite_classical_pvm_haar_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        (unitaryHaar (Fin d × Fin d)).toOuterMeasure (finitePurePVMScoreReachable d K ε) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 10 * (K : ℝ) ^ 10) *
            ε ^ ((pvmCodimension d : ℝ) / 2))) ∧
        (unitaryHaar (Fin d × Fin d)).toOuterMeasure (finiteMixedPVMScoreReachable d K ε) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (d : ℝ) ^ 10 * (K : ℝ) ^ 10) *
            ε ^ ((pvmCodimension d : ℝ) / 2))) :=
  exists_finite_classical_pvm_haar_constant_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

/-- An existing charged universal lower bound at the fifth-power
budget gives the finite-classical tenth-power logarithm estimate. -/
theorem log_le_sixth_tenth_power_of_finite_charged_lower_bound
    {c L : ℝ} {d K : ℕ} (hc : 0 < c) (hd : 0 < d) (hL : 0 ≤ L)
    (hbound : c * (d : ℝ) * Real.sqrt L ≤ (d : ℝ) ^ 4 * (K : ℝ) ^ 5) :
    L ≤ (1 / c ^ 2) * (d : ℝ) ^ 6 * (K : ℝ) ^ 10 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsquare := pow_le_pow_left₀ (by positivity) hbound 2
  rw [mul_pow, mul_pow, Real.sq_sqrt hL] at hsquare
  have hcancel : c ^ 2 * L ≤ (d : ℝ) ^ 6 * (K : ℝ) ^ 10 := by
    apply (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < (d : ℝ) ^ 2)).mp
    calc
      (d : ℝ) ^ 2 * (c ^ 2 * L) = c ^ 2 * (d : ℝ) ^ 2 * L := by ring
      _ ≤ ((d : ℝ) ^ 4 * (K : ℝ) ^ 5) ^ 2 := hsquare
      _ = (d : ℝ) ^ 2 * ((d : ℝ) ^ 6 * (K : ℝ) ^ 10) := by ring
  have hdiv : L ≤ ((d : ℝ) ^ 6 * (K : ℝ) ^ 10) / c ^ 2 := by
    apply (le_div_iff₀ (by positivity : 0 < c ^ 2)).mpr
    simpa only [mul_comm L (c ^ 2)] using hcancel
  convert hdiv using 1
  ring

/-- Universality is quantified over finite-shape target-dependent
protocols. Both pure and common-map mixed scores satisfy the logarithm bound. -/
theorem exists_finite_classical_unitary_universal_log_constant_of_imageVolumeBound
    (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ((∀ U, U ∈ finitePureScoreReachable d K ε) →
          Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) ∧
        ((∀ U, U ∈ finiteMixedScoreReachable d K ε) →
          Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) := by
  obtain ⟨c, hc, hbound⟩ := exists_universal_resource_constant_of_imageVolumeBound hGeom
  refine ⟨1 / c ^ 2, by positivity, ?_⟩
  intro d K hd hK ε hε hεhalf
  have hd0 : 0 < d := by omega
  have hL : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((one_le_div₀ hε).mpr (by linarith))
  have hone := (finiteClassical_charged_budget_admissible hd hK).1
  have hcharged := (hbound d (d ^ 4 * K ^ 5) hd hone ε hε hεhalf).1
  have htransfer (hreach : ∀ U, U ∈ pureReachable d (d ^ 4 * K ^ 5) ε) :
      Real.log (1 / ε) ≤ (1 / c ^ 2) * (d : ℝ) ^ 6 * (K : ℝ) ^ 10 := by
    apply log_le_sixth_tenth_power_of_finite_charged_lower_bound hc hd0 hL
    have h := hcharged hreach
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h
  exact ⟨fun hu => htransfer (fun U =>
      finitePureScoreReachable_subset_pureReachable hd0 ε (hu U)),
    fun hu => htransfer (fun U =>
      finiteMixedScoreReachable_subset_pureReachable hd0 ε (hu U))⟩

/-- The PVM universal conclusion uses full joint-label scores and
the same baseline dimension factor; it is not the stronger unitary rate. -/
theorem exists_finite_classical_pvm_universal_log_constant_of_imageVolumeBound
    (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ((∀ M, M ∈ finitePurePVMScoreReachable d K ε) →
          Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) ∧
        ((∀ M, M ∈ finiteMixedPVMScoreReachable d K ε) →
          Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) := by
  obtain ⟨c, hc, hbound⟩ :=
    exists_pvm_universal_resource_constant_of_imageVolumeBound.{0, 0, 0, 0, 0, 0, 0, 0} hGeom
  refine ⟨1 / c ^ 2, by positivity, ?_⟩
  intro d K hd hK ε hε hεhalf
  have hd0 : 0 < d := by omega
  have hL : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((one_le_div₀ hε).mpr (by linarith))
  have hcharged := (hbound d (d ^ 4 * K ^ 5) hd ε hε hεhalf).1
  have htransfer (hreach : ∀ M, M ∈ purePVMReachable d (d ^ 4 * K ^ 5) ε) :
      Real.log (1 / ε) ≤ (1 / c ^ 2) * (d : ℝ) ^ 6 * (K : ℝ) ^ 10 := by
    apply log_le_sixth_tenth_power_of_finite_charged_lower_bound hc hd0 hL
    have h := hcharged hreach
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h
  exact ⟨fun hu => htransfer (fun M =>
      finitePurePVMScoreReachable_subset_purePVMReachable hd0 ε (hu M)),
    fun hu => htransfer (fun M =>
      finiteMixedPVMScoreReachable_subset_purePVMReachable hd0 ε (hu M))⟩

/-- The finite unitary universal logarithm bound; compression is proved, not assumed. -/
theorem exists_finite_classical_unitary_universal_log_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ((∀ U, U ∈ finitePureScoreReachable d K ε) →
          Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) ∧
        ((∀ U, U ∈ finiteMixedScoreReachable d K ε) →
          Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) :=
  exists_finite_classical_unitary_universal_log_constant_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

/-- The finite PVM universal logarithm bound retains those same three
arguments, the joint-label score and target-dependent protocols. -/
theorem exists_finite_classical_pvm_universal_log_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (d K : ℕ), 2 ≤ d → 1 ≤ K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ((∀ M, M ∈ finitePurePVMScoreReachable d K ε) →
          Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) ∧
        ((∀ M, M ∈ finiteMixedPVMScoreReachable d K ε) →
          Real.log (1 / ε) ≤ C * (d : ℝ) ^ 6 * (K : ℝ) ^ 10) :=
  exists_finite_classical_pvm_universal_log_constant_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

end NLQCLean.ClassicalCommunication

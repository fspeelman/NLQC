import NLQCLean.Bounds.ControlledPhaseLength
import NLQCLean.Bounds.AlmostEveryArithmetic
import Mathlib.Topology.Instances.Rat
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Almost-every fixed controlled-phase charged-footprint rates

The checked interval outer-length estimate yields an exponentially summable
forbidden-error sequence. First Borel–Cantelli and budget/error monotonicity
then give a single constant and a target-dependent threshold valid for all
small errors. The model remains the original charged pure/common-map
finite-mixed model, not a general free-classical or shared-randomness model.
-/

namespace NLQCLean

open MeasureTheory Filter

/-- The interval prefactor is absorbed into a finite initial budget segment.
The forbidden-error coefficient is independent of the interval. -/
theorem controlledPhase_length_rhs_at_forbiddenError_le {C C_J : ℝ} {K : ℕ}
    (hK : 1 ≤ K) (hCJ : C_J ≤ K) :
    C_J * Real.exp (C * (K : ℝ) ^ 2) *
      Real.sqrt (Real.exp (-(2 * (C + 2) * (K : ℝ) ^ 2))) ≤ Real.exp (-(K : ℝ)) := by
  have he : Real.exp (C * (K : ℝ) ^ 2) *
      Real.sqrt (Real.exp (-(2 * (C + 2) * (K : ℝ) ^ 2))) =
      Real.exp (-2 * (K : ℝ) ^ 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  rw [mul_assoc, he]
  calc
    _ ≤ Real.exp (K : ℝ) * Real.exp (-2 * (K : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (hCJ.trans (by linarith [Real.add_one_le_exp (K : ℝ)]))
        (Real.exp_pos _).le
    _ ≤ _ := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
      nlinarith

/-- Reachable angles increase with both the charged budget and the allowed
score error. The interval restriction itself remains fixed. -/
theorem chargedControlledPhaseAngles_mono {K K' : ℕ} {ε ε' : ℝ} {J : Set ℝ}
    (hK : K ≤ K') (hε : ε ≤ ε') :
    chargedControlledPhaseAngles K ε J ⊆ chargedControlledPhaseAngles K' ε' J := by
  rintro θ ⟨hθ, hreach⟩
  exact ⟨hθ, pureReachable_mono hK hε hreach⟩

/-- A universal forbidden-error coefficient works on every nondegenerate
semicircle interval. The starting budget depends on the target and interval. -/
theorem exists_ae_chargedControlledPhase_forbidden_error_constant
    (hGeom : PolynomialImageVolumeBound) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (a b : ℝ), a ≤ b →
      ((0 < a ∧ b < Real.pi) ∨ (Real.pi < a ∧ b < 2 * Real.pi)) →
      ∀ᵐ θ ∂volume, ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
        θ ∉ chargedControlledPhaseAngles K (Real.exp (-(A * (K : ℝ) ^ 2))) (Set.Icc a b) := by
  obtain ⟨C, hC, hlength⟩ := exists_chargedControlledPhase_length_constant hGeom
  refine ⟨2 * (C + 2), by linarith, ?_⟩
  intro a b hab hsemicircle
  obtain ⟨C_J, _, hbound⟩ := hlength a b hab hsemicircle
  apply ae_exists_forall_notMem_of_le_exp_neg volume _ (Nat.ceil C_J + 1)
  intro K hK
  have hK1 : 1 ≤ K := by omega
  have hCJ : C_J ≤ (K : ℝ) := by
    have hn : (Nat.ceil C_J : ℝ) ≤ K := by exact_mod_cast (show Nat.ceil C_J ≤ K by omega)
    exact (Nat.le_ceil C_J).trans hn
  exact (hbound K hK1 _ (Real.exp_pos _)).trans
    (ENNReal.ofReal_le_ofReal (controlledPhase_length_rhs_at_forbiddenError_le hK1 hCJ))

/-- On each compact interval in either open semicircle, one universal resource
constant precedes the target-dependent small-error threshold and all budgets. -/
theorem exists_ae_chargedControlledPhase_interval_resource_constant
    (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a b : ℝ), a ≤ b →
      ((0 < a ∧ b < Real.pi) ∨ (Real.pi < a ∧ b < 2 * Real.pi)) →
      ∀ᵐ θ ∂volume, θ ∈ Set.Icc a b →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          (controlledPhaseTarget θ ∈ pureReachable 2 K ε →
            c * Real.sqrt (Real.log (1 / ε)) ≤ K) ∧
          (controlledPhaseTarget θ ∈ mixedReachable 2 K ε →
            c * Real.sqrt (Real.log (1 / ε)) ≤ K) := by
  obtain ⟨A, hA, hforbidden⟩ := exists_ae_chargedControlledPhase_forbidden_error_constant hGeom
  have hA0 : 0 < A := by linarith
  refine ⟨1 / Real.sqrt A, by positivity, ?_⟩
  intro a b hab hsemicircle
  filter_upwards [hforbidden a b hab hsemicircle] with θ hθ
  intro hmem
  obtain ⟨K₀, hK₀, havoid⟩ := hθ
  have hthreshold := forbiddenError_threshold_mem hA (d := 1) (K₀ := K₀) (by decide)
    (by simpa using hK₀)
  simp only [Nat.cast_one, one_pow, div_one] at hthreshold
  refine ⟨Real.exp (-(A * (K₀ : ℝ) ^ 2)), hthreshold.1, hthreshold.2, ?_⟩
  intro K ε _hε hε₀
  have hbound : controlledPhaseTarget θ ∈ pureReachable 2 K ε →
      1 / Real.sqrt A * Real.sqrt (Real.log (1 / ε)) ≤ K := by
    intro hreach
    have h := resource_lower_of_forbiddenError
      (R := fun K ε => chargedControlledPhaseAngles K ε (Set.Icc a b))
      (fun hK hε => chargedControlledPhaseAngles_mono hK hε) hA0 (d := 1) (by decide)
      (x := θ) (K₀ := K₀)
      (by simpa only [Nat.cast_one, one_pow, div_one] using havoid)
      (by simpa only [Nat.cast_one, one_pow, div_one] using hε₀) ⟨hmem, hreach⟩
    simpa only [Nat.cast_one, mul_one] using h
  refine ⟨hbound, ?_⟩
  rw [mixedReachable_eq_pureReachable]
  exact hbound

/-- Rational compact intervals exhaust both open semicircles. Their common
resource constant survives the countable intersection of conull sets; only
the error threshold depends on the fixed angle. The three endpoints are null. -/
theorem exists_ae_chargedControlledPhase_resource_constant
    (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ θ ∂volume.restrict (Set.Icc 0 (2 * Real.pi)),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        (controlledPhaseTarget θ ∈ pureReachable 2 K ε →
          c * Real.sqrt (Real.log (1 / ε)) ≤ K) ∧
        (controlledPhaseTarget θ ∈ mixedReachable 2 K ε →
          c * Real.sqrt (Real.log (1 / ε)) ≤ K) := by
  obtain ⟨c, hc, hinterval⟩ := exists_ae_chargedControlledPhase_interval_resource_constant hGeom
  refine ⟨c, hc, ?_⟩
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  have hrat : ∀ᵐ θ ∂volume, ∀ a b : ℚ, (a : ℝ) ≤ b →
      ((0 < (a : ℝ) ∧ (b : ℝ) < Real.pi) ∨
        (Real.pi < (a : ℝ) ∧ (b : ℝ) < 2 * Real.pi)) →
      θ ∈ Set.Icc (a : ℝ) (b : ℝ) →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        (controlledPhaseTarget θ ∈ pureReachable 2 K ε →
          c * Real.sqrt (Real.log (1 / ε)) ≤ K) ∧
        (controlledPhaseTarget θ ∈ mixedReachable 2 K ε →
          c * Real.sqrt (Real.log (1 / ε)) ≤ K) := by
    apply eventually_countable_forall.mpr
    intro a
    apply eventually_countable_forall.mpr
    intro b
    by_cases hab : (a : ℝ) ≤ b
    · by_cases hs : ((0 < (a : ℝ) ∧ (b : ℝ) < Real.pi) ∨
          (Real.pi < (a : ℝ) ∧ (b : ℝ) < 2 * Real.pi))
      · exact (hinterval a b hab hs).mono (fun _ h _ _ => h)
      · exact Eventually.of_forall (fun _ _ h => (hs h).elim)
    · exact Eventually.of_forall (fun _ h => (hab h).elim)
  filter_upwards [hrat, volume.ae_ne (0 : ℝ), volume.ae_ne Real.pi,
    volume.ae_ne (2 * Real.pi)] with θ hθ hne0 hnepi hne2pi
  intro hmem
  have h0 : 0 < θ := lt_of_le_of_ne hmem.1 hne0.symm
  have h2pi : θ < 2 * Real.pi := lt_of_le_of_ne hmem.2 hne2pi
  rcases lt_or_gt_of_ne hnepi with hupper | hlower
  · obtain ⟨a, ha0, haθ⟩ := exists_rat_btwn h0
    obtain ⟨b, hθb, hbpi⟩ := exists_rat_btwn hupper
    exact hθ a b (haθ.le.trans hθb.le) (Or.inl ⟨ha0, hbpi⟩) ⟨haθ.le, hθb.le⟩
  · obtain ⟨a, hapi, haθ⟩ := exists_rat_btwn hlower
    obtain ⟨b, hθb, hb2pi⟩ := exists_rat_btwn h2pi
    exact hθ a b (haθ.le.trans hθb.le) (Or.inr ⟨hapi, hb2pi⟩) ⟨haθ.le, hθb.le⟩

/-- Exactly the existing three geometry inputs; the threshold is chosen after
the fixed phase and before every charged budget and allowed score error. -/
theorem exists_ae_chargedControlledPhase_resource_constant_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ θ ∂volume.restrict (Set.Icc 0 (2 * Real.pi)),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        (controlledPhaseTarget θ ∈ pureReachable 2 K ε →
          c * Real.sqrt (Real.log (1 / ε)) ≤ K) ∧
        (controlledPhaseTarget θ ∈ mixedReachable 2 K ε →
          c * Real.sqrt (Real.log (1 / ε)) ≤ K) :=
  exists_ae_chargedControlledPhase_resource_constant
    (ProvedProjection.polynomialImageVolumeBound_of_external hLRT hStratification hComponents)

end NLQCLean

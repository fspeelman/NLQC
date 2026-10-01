import NLQCLean.Bounds.ControlledPhaseLength
import NLQCLean.Models.ClassicalCommunication.FiniteReachability

/-!
# Outer length and worst-case phases for finite classical protocols

The angle sets use twelve-entry finite shapes, pure resources or
common-map finite mixtures, and the original normalized unitary score.
Proved compression transfers that score at charged footprint `64 Kq⁵`;
it does not assert preservation of operational error. Outer measure needs
no measurability certificate. No arbitrary-register reindexing,
standard-Borel or shared-randomness extension is asserted.
-/

namespace NLQCLean

open MeasureTheory ClassicalCommunication

/-- Finite-shape pure score reachability in an angle set. -/
def finitePureControlledPhaseAngles (Kq : ℕ) (ε : ℝ) (J : Set ℝ) : Set ℝ :=
  {θ | θ ∈ J ∧ controlledPhaseTarget θ ∈ finitePureScoreReachable 2 Kq ε}

/-- Common-map finite-mixed score reachability in an angle set. -/
def finiteMixedControlledPhaseAngles (Kq : ℕ) (ε : ℝ) (J : Set ℝ) : Set ℝ :=
  {θ | θ ∈ J ∧ controlledPhaseTarget θ ∈ finiteMixedScoreReachable 2 Kq ε}

/-- Pure score transfer preserves the original budget and error as inputs;
only the output charged budget is enlarged. -/
theorem finitePureControlledPhaseAngles_subset_charged (Kq : ℕ) (ε : ℝ) (J : Set ℝ) :
    finitePureControlledPhaseAngles Kq ε J ⊆
      chargedControlledPhaseAngles (64 * Kq ^ 5) ε J := by
  rintro θ ⟨hθ, hreach⟩
  refine ⟨hθ, ?_⟩
  simpa only [show 4 * 2 ^ 4 = (64 : ℕ) by norm_num] using
    finitePureScoreReachable_subset_pureReachable (by decide : 0 < 2) ε hreach

/-- Mixed transfer chooses a rank-capped component and transfers its
score, without changing the error in the score inequality. -/
theorem finiteMixedControlledPhaseAngles_subset_charged (Kq : ℕ) (ε : ℝ) (J : Set ℝ) :
    finiteMixedControlledPhaseAngles Kq ε J ⊆
      chargedControlledPhaseAngles (64 * Kq ^ 5) ε J := by
  rintro θ ⟨hθ, hreach⟩
  refine ⟨hθ, ?_⟩
  simpa only [show 4 * 2 ^ 4 = (64 : ℕ) by norm_num] using
    finiteMixedScoreReachable_subset_pureReachable (by decide : 0 < 2) ε hreach

/-- Both classes lie in the same charged set, so their union needs no
additional factor in the outer-length estimate. -/
theorem finiteControlledPhaseAngles_union_subset_charged (Kq : ℕ) (ε : ℝ) (J : Set ℝ) :
    finitePureControlledPhaseAngles Kq ε J ∪ finiteMixedControlledPhaseAngles Kq ε J ⊆
      chargedControlledPhaseAngles (64 * Kq ^ 5) ε J := by
  intro θ hθ
  rcases hθ with hp | hm
  · exact finitePureControlledPhaseAngles_subset_charged Kq ε J hp
  · exact finiteMixedControlledPhaseAngles_subset_charged Kq ε J hm

theorem finitePureControlledPhaseAngles_zero_budget (ε : ℝ) (J : Set ℝ) :
    finitePureControlledPhaseAngles 0 ε J = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro θ ⟨_, hreach⟩
  rw [finitePureScoreReachable_zero_budget (by decide : 0 < 2) ε] at hreach
  exact hreach

theorem finiteMixedControlledPhaseAngles_zero_budget (ε : ℝ) (J : Set ℝ) :
    finiteMixedControlledPhaseAngles 0 ε J = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro θ ⟨_, hreach⟩
  rw [finiteMixedScoreReachable_zero_budget (by decide : 0 < 2) ε] at hreach
  exact hreach

/-- Substituting the two-qubit charged budget multiplies the universal
exponential coefficient by `4096`. -/
theorem finiteControlledPhase_charged_exponent_eq (C : ℝ) (Kq : ℕ) :
    C * ((64 * Kq ^ 5 : ℕ) : ℝ) ^ 2 = (4096 * C) * (Kq : ℝ) ^ 10 := by
  push_cast
  ring

/-- One universal coefficient precedes the interval. The interval prefactor
then bounds both honest finite angle sets and their union, in outer measure. -/
theorem exists_finiteControlledPhase_length_constant
    (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (a b : ℝ), a ≤ b →
      ((0 < a ∧ b < Real.pi) ∨ (Real.pi < a ∧ b < 2 * Real.pi)) →
      ∃ C_J : ℝ, 0 < C_J ∧ ∀ (Kq : ℕ), 1 ≤ Kq → ∀ (ε : ℝ), 0 < ε →
        volume (finitePureControlledPhaseAngles Kq ε (Set.Icc a b) ∪
          finiteMixedControlledPhaseAngles Kq ε (Set.Icc a b)) ≤
            ENNReal.ofReal (C_J * Real.exp (C * (Kq : ℝ) ^ 10) * Real.sqrt ε) ∧
        volume (finitePureControlledPhaseAngles Kq ε (Set.Icc a b)) ≤
          ENNReal.ofReal (C_J * Real.exp (C * (Kq : ℝ) ^ 10) * Real.sqrt ε) ∧
        volume (finiteMixedControlledPhaseAngles Kq ε (Set.Icc a b)) ≤
          ENNReal.ofReal (C_J * Real.exp (C * (Kq : ℝ) ^ 10) * Real.sqrt ε) := by
  obtain ⟨C, hC, hlength⟩ := exists_chargedControlledPhase_length_constant hGeom
  refine ⟨4096 * C, by linarith, ?_⟩
  intro a b hab hsemicircle
  obtain ⟨C_J, hCJ, hbound⟩ := hlength a b hab hsemicircle
  refine ⟨C_J, hCJ, ?_⟩
  intro Kq hKq ε hε
  have hKbar : 1 ≤ 64 * Kq ^ 5 := by
    have hKq0 : 0 < Kq := by omega
    have hpos : 0 < 64 * Kq ^ 5 := by positivity
    omega
  have hcharged := hbound (64 * Kq ^ 5) hKbar ε hε
  rw [finiteControlledPhase_charged_exponent_eq] at hcharged
  have hunion := (measure_mono
    (finiteControlledPhaseAngles_union_subset_charged Kq ε (Set.Icc a b))).trans hcharged
  refine ⟨hunion, ?_, ?_⟩
  · exact (measure_mono Set.subset_union_left).trans hunion
  · exact (measure_mono Set.subset_union_right).trans hunion

/-- An explicit exponential error threshold makes the length bound strictly
smaller than a prescribed positive interval length. -/
theorem phase_length_rhs_lt_of_exponential_threshold {A l t ε : ℝ}
    (hA : 0 < A) (hl : 0 < l)
    (hε : ε < (l / A) ^ 2 * Real.exp (-(2 * t))) :
    A * Real.exp t * Real.sqrt ε < l := by
  have hroot : Real.sqrt ε < (l / A) * Real.exp (-t) := by
    apply (Real.sqrt_lt' (mul_pos (div_pos hl hA) (Real.exp_pos _))).mpr
    calc
      ε < (l / A) ^ 2 * Real.exp (-(2 * t)) := hε
      _ = ((l / A) * Real.exp (-t)) ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        norm_num
  have he : A * Real.exp t * ((l / A) * Real.exp (-t)) = l := by
    calc
      _ = l * (Real.exp t * Real.exp (-t)) := by field_simp [hA.ne']
      _ = l := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  exact (mul_lt_mul_of_pos_left hroot (mul_pos hA (Real.exp_pos t))).trans_eq he

/-- A strict outer-length deficit supplies a point outside the set without
assuming that set is measurable. -/
theorem exists_phase_notMem_of_outer_length_lt {S : Set ℝ} {a b : ℝ}
    (hvolume : volume S < volume (Set.Icc a b)) :
    ∃ θ : ℝ, θ ∈ Set.Icc a b ∧ θ ∉ S := by
  by_contra h
  have hsub : Set.Icc a b ⊆ S := by
    intro θ hθ
    by_contra hn
    exact h ⟨θ, hθ, hn⟩
  exact (not_lt_of_ge (measure_mono hsub)) hvolume

/-- Every nondegenerate compact semicircle interval contains a worst-case
phase at each error below its explicit exponential budget threshold. The same
phase defeats both pure and common-map finite-mixed score reachability. -/
theorem exists_finiteControlledPhase_worst_case_constant
    (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (a b : ℝ), a < b →
      ((0 < a ∧ b < Real.pi) ∨ (Real.pi < a ∧ b < 2 * Real.pi)) →
      ∃ ε_J : ℝ, 0 < ε_J ∧ ∀ (Kq : ℕ), 1 ≤ Kq → ∀ (ε : ℝ), 0 < ε →
        ε < ε_J * Real.exp (-(2 * C * (Kq : ℝ) ^ 10)) →
        ∃ θ : ℝ, θ ∈ Set.Icc a b ∧
          controlledPhaseTarget θ ∉ finitePureScoreReachable 2 Kq ε ∧
          controlledPhaseTarget θ ∉ finiteMixedScoreReachable 2 Kq ε := by
  obtain ⟨C, hC, hlength⟩ := exists_finiteControlledPhase_length_constant hGeom
  refine ⟨C, hC, ?_⟩
  intro a b hab hsemicircle
  obtain ⟨C_J, hCJ, hbound⟩ := hlength a b hab.le hsemicircle
  have hba : 0 < b - a := sub_pos.mpr hab
  refine ⟨((b - a) / C_J) ^ 2, by positivity, ?_⟩
  intro Kq hKq ε hε hthreshold
  have hlengthlt : C_J * Real.exp (C * (Kq : ℝ) ^ 10) * Real.sqrt ε < b - a := by
    apply phase_length_rhs_lt_of_exponential_threshold hCJ hba
    simpa only [mul_assoc] using hthreshold
  have hvolume : volume (finitePureControlledPhaseAngles Kq ε (Set.Icc a b) ∪
      finiteMixedControlledPhaseAngles Kq ε (Set.Icc a b)) < volume (Set.Icc a b) := by
    refine ((hbound Kq hKq ε hε).1).trans_lt ?_
    rw [Real.volume_Icc]
    exact (ENNReal.ofReal_lt_ofReal_iff (sub_pos.mpr hab)).mpr hlengthlt
  obtain ⟨θ, hθ, hn⟩ := exists_phase_notMem_of_outer_length_lt hvolume
  refine ⟨θ, hθ, ?_, ?_⟩
  · intro hp
    exact hn (Or.inl ⟨hθ, hp⟩)
  · intro hm
    exact hn (Or.inr ⟨hθ, hm⟩)

/-- The finite outer-length bound retains exactly the three geometry inputs. -/
theorem exists_finiteControlledPhase_length_constant_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (a b : ℝ), a ≤ b →
      ((0 < a ∧ b < Real.pi) ∨ (Real.pi < a ∧ b < 2 * Real.pi)) →
      ∃ C_J : ℝ, 0 < C_J ∧ ∀ (Kq : ℕ), 1 ≤ Kq → ∀ (ε : ℝ), 0 < ε →
        volume (finitePureControlledPhaseAngles Kq ε (Set.Icc a b) ∪
          finiteMixedControlledPhaseAngles Kq ε (Set.Icc a b)) ≤
            ENNReal.ofReal (C_J * Real.exp (C * (Kq : ℝ) ^ 10) * Real.sqrt ε) ∧
        volume (finitePureControlledPhaseAngles Kq ε (Set.Icc a b)) ≤
          ENNReal.ofReal (C_J * Real.exp (C * (Kq : ℝ) ^ 10) * Real.sqrt ε) ∧
        volume (finiteMixedControlledPhaseAngles Kq ε (Set.Icc a b)) ≤
          ENNReal.ofReal (C_J * Real.exp (C * (Kq : ℝ) ^ 10) * Real.sqrt ε) :=
  exists_finiteControlledPhase_length_constant
    (ProvedProjection.polynomialImageVolumeBound_of_external hLRT hStratification hComponents)

/-- The simultaneous finite pure/mixed worst-case phase needs no additional
arithmetic, compression or measurability contract. -/
theorem exists_finiteControlledPhase_worst_case_constant_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (a b : ℝ), a < b →
      ((0 < a ∧ b < Real.pi) ∨ (Real.pi < a ∧ b < 2 * Real.pi)) →
      ∃ ε_J : ℝ, 0 < ε_J ∧ ∀ (Kq : ℕ), 1 ≤ Kq → ∀ (ε : ℝ), 0 < ε →
        ε < ε_J * Real.exp (-(2 * C * (Kq : ℝ) ^ 10)) →
        ∃ θ : ℝ, θ ∈ Set.Icc a b ∧
          controlledPhaseTarget θ ∉ finitePureScoreReachable 2 Kq ε ∧
          controlledPhaseTarget θ ∉ finiteMixedScoreReachable 2 Kq ε :=
  exists_finiteControlledPhase_worst_case_constant
    (ProvedProjection.polynomialImageVolumeBound_of_external hLRT hStratification hComponents)

end NLQCLean

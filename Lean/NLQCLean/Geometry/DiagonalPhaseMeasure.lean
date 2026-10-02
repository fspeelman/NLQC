import NLQCLean.Invariants.RectangularControlledPhase
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Uniform alternating phases of rectangular diagonal unitaries

Independent phases use the normalized interval law on `(0, 2π]`. The alternating
four-entry angle, reduced modulo `2π`, has that same law. On the phase torus it is
a continuous surjective additive homomorphism, so translation invariance of Haar
measure gives the exact pushforward. The interval representative preserves this
law and does not change the physical controlled-phase matrix.
-/

namespace NLQCLean

open MeasureTheory Set
open scoped ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The additive circle of physical phases modulo `2π`. -/
abbrev PhaseCircle := AddCircle (2 * Real.pi)

/-- Probability Haar measure on the physical phase circle. -/
noncomputable def phaseCircleHaar : Measure PhaseCircle :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume

/-- Uniform probability law for a phase represented in `(0, 2π]`. -/
noncomputable def phaseIntervalMeasure : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Ioc 0 (2 * Real.pi))

instance phaseCircleHaar_isProbabilityMeasure : IsProbabilityMeasure phaseCircleHaar := by
  constructor
  simp only [phaseCircleHaar, Measure.smul_apply, smul_eq_mul, AddCircle.measure_univ]
  exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

instance phaseIntervalMeasure_isProbabilityMeasure : IsProbabilityMeasure phaseIntervalMeasure := by
  constructor
  simp only [phaseIntervalMeasure, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
    Real.volume_Ioc, sub_zero]
  exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

instance phaseCircleHaar_isAddHaarMeasure : phaseCircleHaar.IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.smul volume
    (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
    (ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr (by positivity)).ne'))

/-- The representative in `(0, 2π]`. -/
noncomputable def phaseCircleRepresentative (θ : PhaseCircle) : ℝ :=
  AddCircle.equivIoc (2 * Real.pi) 0 θ

set_option backward.isDefEq.respectTransparency.types false in
theorem measurePreserving_phaseCircleRepresentative :
    MeasurePreserving phaseCircleRepresentative phaseCircleHaar phaseIntervalMeasure := by
  have h := (measurePreserving_subtype_coe measurableSet_Ioc).comp
    (AddCircle.measurePreserving_equivIoc (2 * Real.pi) (a := 0))
  simpa only [phaseCircleRepresentative, phaseCircleHaar, phaseIntervalMeasure,
    Function.comp_def, zero_add] using! h.smul_measure (ENNReal.ofReal (2 * Real.pi))⁻¹

theorem measurePreserving_phaseCircle_coe :
    MeasurePreserving ((↑) : ℝ → PhaseCircle) phaseIntervalMeasure phaseCircleHaar := by
  simpa only [phaseCircleHaar, phaseIntervalMeasure, zero_add] using
    (AddCircle.measurePreserving_mk (2 * Real.pi) 0).smul_measure
      (ENNReal.ofReal (2 * Real.pi))⁻¹

/-- The alternating four-entry phase as an additive homomorphism of the torus. -/
noncomputable def rectangularAlternatingPhase {dA dB : ℕ} (hA : 2 ≤ dA) (hB : 2 ≤ dB) :
    (Fin dA × Fin dB → PhaseCircle) →+ PhaseCircle where
  toFun θ :=
    θ ((twoLevelEmbedding hA) 1, (twoLevelEmbedding hB) 1) -
      θ ((twoLevelEmbedding hA) 1, (twoLevelEmbedding hB) 0) -
      θ ((twoLevelEmbedding hA) 0, (twoLevelEmbedding hB) 1) +
      θ ((twoLevelEmbedding hA) 0, (twoLevelEmbedding hB) 0)
  map_zero' := by simp
  map_add' := by intro θ φ; simp only [Pi.add_apply]; abel

theorem continuous_rectangularAlternatingPhase {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) : Continuous (rectangularAlternatingPhase hA hB) := by
  change Continuous (fun θ : Fin dA × Fin dB → PhaseCircle =>
    θ ((twoLevelEmbedding hA) 1, (twoLevelEmbedding hB) 1) -
      θ ((twoLevelEmbedding hA) 1, (twoLevelEmbedding hB) 0) -
      θ ((twoLevelEmbedding hA) 0, (twoLevelEmbedding hB) 1) +
      θ ((twoLevelEmbedding hA) 0, (twoLevelEmbedding hB) 0))
  fun_prop

theorem surjective_rectangularAlternatingPhase {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) : Function.Surjective (rectangularAlternatingPhase hA hB) := by
  intro z
  let p := ((twoLevelEmbedding hA) 1, (twoLevelEmbedding hB) 1)
  have h10 : ((twoLevelEmbedding hA) 1, (twoLevelEmbedding hB) 0) ≠ p := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1) ((twoLevelEmbedding hB).injective (congrArg Prod.snd h))
  have h01 : ((twoLevelEmbedding hA) 0, (twoLevelEmbedding hB) 1) ≠ p := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1) ((twoLevelEmbedding hA).injective (congrArg Prod.fst h))
  have h00 : ((twoLevelEmbedding hA) 0, (twoLevelEmbedding hB) 0) ≠ p := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1) ((twoLevelEmbedding hA).injective (congrArg Prod.fst h))
  refine ⟨fun q => if q = p then z else 0, ?_⟩
  simp [rectangularAlternatingPhase, h10, h01, h00, p]

/-- Independent uniform torus phases have an exactly uniform alternating phase. -/
theorem measurePreserving_rectangularAlternatingPhase {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) :
    MeasurePreserving (rectangularAlternatingPhase hA hB)
      (Measure.pi fun _ : Fin dA × Fin dB => phaseCircleHaar) phaseCircleHaar :=
  (rectangularAlternatingPhase hA hB).measurePreserving
    (continuous_rectangularAlternatingPhase hA hB)
    (surjective_rectangularAlternatingPhase hA hB) (by simp)

/-- Independent uniform real representatives of all rectangular phases. -/
noncomputable def rectangularPhaseMeasure (dA dB : ℕ) :
    Measure (Fin dA × Fin dB → ℝ) := Measure.pi fun _ => phaseIntervalMeasure

/-- The alternating angle reduced to its representative in `(0, 2π]`. -/
noncomputable def rectangularAlternatingAngleMod {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ) : ℝ :=
  phaseCircleRepresentative (rectangularAlternatingAngle hA hB θ : PhaseCircle)

/-- The mod-`2π` alternating angle pushes the independent interval law forward
to the same uniform interval law. -/
theorem measurePreserving_rectangularAlternatingAngleMod {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) :
    MeasurePreserving (rectangularAlternatingAngleMod hA hB)
      (rectangularPhaseMeasure dA dB) phaseIntervalMeasure := by
  have hpi := measurePreserving_pi (fun _ : Fin dA × Fin dB => phaseIntervalMeasure)
    (fun _ : Fin dA × Fin dB => phaseCircleHaar) (fun _ => measurePreserving_phaseCircle_coe)
  convert measurePreserving_phaseCircleRepresentative.comp
    ((measurePreserving_rectangularAlternatingPhase hA hB).comp hpi) using 1
  · ext θ
    rfl
  · rfl

/-- Choosing the interval representative modulo `2π` leaves the physical
controlled-phase matrix unchanged. -/
theorem controlledPhase_phaseCircleRepresentative_coe (θ : ℝ) :
    controlledPhase (phaseCircleRepresentative (θ : PhaseCircle)) = controlledPhase θ := by
  have hcoe : (phaseCircleRepresentative (θ : PhaseCircle) : PhaseCircle) =
      (θ : PhaseCircle) := AddCircle.coe_equivIoc
  have hcircle := congrArg Real.Angle.toCircle hcoe
  have hexp := congrArg (fun z : Circle => (z : ℂ)) hcircle
  change Complex.exp ((phaseCircleRepresentative (θ : PhaseCircle) : ℂ) * Complex.I) =
    Complex.exp ((θ : ℂ) * Complex.I) at hexp
  exact congrArg qubitCornerPhase hexp

/-- The mod-`2π` angle and the unmodified alternating angle define the same gate. -/
theorem controlledPhase_rectangularAlternatingAngleMod {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ) :
    controlledPhase (rectangularAlternatingAngleMod hA hB θ) =
      controlledPhase (rectangularAlternatingAngle hA hB θ) :=
  controlledPhase_phaseCircleRepresentative_coe _

/-- Any conull angle predicate for the usual closed interval pulls back to
independent rectangular phases. No measurability of the predicate is needed. -/
theorem ae_rectangularAlternatingAngleMod_of_ae {dA dB : ℕ}
    (hA : 2 ≤ dA) (hB : 2 ≤ dB) {P : ℝ → Prop}
    (hP : ∀ᵐ θ ∂volume.restrict (Icc 0 (2 * Real.pi)), P θ) :
    ∀ᵐ θ ∂rectangularPhaseMeasure dA dB, P (rectangularAlternatingAngleMod hA hB θ) := by
  have hIoc := ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hP
  have hprob : ∀ᵐ θ ∂phaseIntervalMeasure, P θ :=
    Measure.ae_smul_measure hIoc (ENNReal.ofReal (2 * Real.pi))⁻¹
  exact (measurePreserving_rectangularAlternatingAngleMod hA hB).quasiMeasurePreserving.ae hprob

end NLQCLean

import NLQCLean.Geometry.UnitaryNormalEmbedding
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Probability Haar measure on the finite unitary group

The matrix group carries its Borel topology and Haar measure normalized
on the whole compact group. Finite invariant measures are its scalar multiples.
-/

namespace NLQCLean

open MeasureTheory TopologicalSpace
open scoped ENNReal

/-- Probability Haar measure, normalized on the entire compact unitary group. -/
noncomputable def unitaryHaar (n : Type*) [Fintype n] [DecidableEq n] :
    Measure (Matrix.unitaryGroup n ℂ) :=
  Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

instance isProbabilityMeasure_unitaryHaar (n : Type*) [Fintype n] [DecidableEq n] :
    IsProbabilityMeasure (unitaryHaar n) := ⟨Measure.haarMeasure_self⟩

instance isHaarMeasure_unitaryHaar (n : Type*) [Fintype n] [DecidableEq n] :
    (unitaryHaar n).IsHaarMeasure := by
  unfold unitaryHaar
  infer_instance

theorem unitaryHaar_univ (n : Type*) [Fintype n] [DecidableEq n] :
    unitaryHaar n Set.univ = 1 := measure_univ

/-- Haar uniqueness, including the zero invariant measure. -/
theorem unitary_invariant_measure_eq_smul (n : Type*) [Fintype n] [DecidableEq n]
    (ν : Measure (Matrix.unitaryGroup n ℂ)) [IsFiniteMeasure ν] [ν.IsMulLeftInvariant] :
    ν = ν Set.univ • unitaryHaar n := by
  have he := Measure.isMulInvariant_eq_smul_of_compactSpace ν (unitaryHaar n)
  have hm : (ν.haarScalarFactor (unitaryHaar n) : ℝ≥0∞) = ν Set.univ := by
    have hm := congrArg (fun μ : Measure (Matrix.unitaryGroup n ℂ) => μ Set.univ) he
    simpa only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, unitaryHaar_univ, mul_one] using hm.symm
  ext S hS
  have h := congrArg (fun μ : Measure (Matrix.unitaryGroup n ℂ) => μ S) he
  simpa only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hm] using h

end NLQCLean

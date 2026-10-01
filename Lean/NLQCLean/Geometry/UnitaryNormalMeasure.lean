import NLQCLean.Geometry.UnitaryNormalCoordinates
import NLQCLean.Geometry.UnitaryHaar
import Mathlib.MeasureTheory.Measure.Comap

/-!
# The finite normal-image measure

Pull back ambient Euclidean volume through the proved normal
embedding, restrict to the open normal radius, and project to the unitary.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius ENNReal

variable (n : Type*) [Fintype n] [DecidableEq n]

def normalSlice (s : ℝ) : Set (UnitaryNormalDomain n) := {z | ‖z.2.1‖ < s}

theorem measurableSet_normalSlice (s : ℝ) : MeasurableSet (normalSlice n s) := by
  have hc : Continuous (fun z : UnitaryNormalDomain n => ‖z.2.1‖) := by fun_prop
  exact (isOpen_lt hc continuous_const).measurableSet

/-- Pullback along the closed measurable embedding, with Euclidean volume. -/
noncomputable def normalDomainVolume : Measure (UnitaryNormalDomain n) :=
  volume.comap (normalEuclideanMap n)

theorem normalDomainVolume_apply {S : Set (UnitaryNormalDomain n)} (hS : MeasurableSet S) :
    normalDomainVolume n S = volume (normalEuclideanMap n '' S) :=
  Measure.comap_apply _ (measurableEmbedding_normalEuclideanMap n).injective
    (fun _ h => (measurableEmbedding_normalEuclideanMap n).measurableSet_image.mpr h) volume hS

instance isFiniteMeasure_normalDomainVolume : IsFiniteMeasure (normalDomainVolume n) where
  measure_univ_lt_top := by
    rw [normalDomainVolume_apply n MeasurableSet.univ, Set.image_univ]
    exact (isCompact_range_normalEuclideanMap n).measure_lt_top

/-- The normal-image measure, for every real radius. -/
noncomputable def unitaryNormalMeasure (s : ℝ) : Measure (Matrix.unitaryGroup n ℂ) :=
  ((normalDomainVolume n).restrict (normalSlice n s)).map Prod.fst

instance isFiniteMeasure_unitaryNormalMeasure (s : ℝ) : IsFiniteMeasure (unitaryNormalMeasure n s) := by
  unfold unitaryNormalMeasure
  infer_instance

/-- Exact Borel-set evaluation as the ambient volume of the normal image. -/
theorem unitaryNormalMeasure_apply (s : ℝ) {S : Set (Matrix.unitaryGroup n ℂ)}
    (hS : MeasurableSet S) :
    unitaryNormalMeasure n s S =
      volume (normalEuclideanMap n '' {z : UnitaryNormalDomain n | z.1 ∈ S ∧ ‖z.2.1‖ < s}) := by
  rw [unitaryNormalMeasure, Measure.map_apply continuous_fst.measurable hS,
    Measure.restrict_apply (continuous_fst.measurable hS),
    normalDomainVolume_apply n ((continuous_fst.measurable hS).inter (measurableSet_normalSlice n s))]
  rfl

theorem normalImage_preimage_left_mul (s : ℝ) (U : Matrix.unitaryGroup n ℂ)
    (S : Set (Matrix.unitaryGroup n ℂ)) :
    normalEuclideanMap n '' {z : UnitaryNormalDomain n | U * z.1 ∈ S ∧ ‖z.2.1‖ < s} =
      unitaryLeftEuclidean U ⁻¹'
        (normalEuclideanMap n '' {z : UnitaryNormalDomain n | z.1 ∈ S ∧ ‖z.2.1‖ < s}) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(U * z.1, z.2), hz, normalEuclideanMap_left_mul U z⟩
  · rintro ⟨w, hw, he⟩
    refine ⟨(U⁻¹ * w.1, w.2), ⟨by simpa using hw.1, hw.2⟩, ?_⟩
    apply (unitaryLeftEuclidean U).injective
    rw [← normalEuclideanMap_left_mul]
    simpa using he

instance isMulLeftInvariant_unitaryNormalMeasure (s : ℝ) :
    (unitaryNormalMeasure n s).IsMulLeftInvariant := by
  apply (forall_measure_preimage_mul_iff _).mp
  intro U S hS
  have hpre : MeasurableSet ((fun V => U * V) ⁻¹' S) := (continuous_const_mul U).measurable hS
  rw [unitaryNormalMeasure_apply n s hpre, unitaryNormalMeasure_apply n s hS]
  change volume (normalEuclideanMap n '' {z : UnitaryNormalDomain n | U * z.1 ∈ S ∧ ‖z.2.1‖ < s}) = _
  rw [normalImage_preimage_left_mul]
  apply (measurePreserving_unitaryLeftEuclidean U).measure_preimage
  apply MeasurableSet.nullMeasurableSet
  apply (measurableEmbedding_normalEuclideanMap n).measurableSet_image.mpr
  exact (continuous_fst.measurable hS).inter (measurableSet_normalSlice n s)

/-- The normal-image measure is its total mass times probability Haar. -/
theorem unitaryNormalMeasure_eq_smul (s : ℝ) :
    unitaryNormalMeasure n s = unitaryNormalMeasure n s Set.univ • unitaryHaar n :=
  unitary_invariant_measure_eq_smul n (unitaryNormalMeasure n s)

theorem normalImageVolume_eq_total_mul_haar (s : ℝ) {S : Set (Matrix.unitaryGroup n ℂ)}
    (hS : MeasurableSet S) :
    volume (normalEuclideanMap n '' {z : UnitaryNormalDomain n | z.1 ∈ S ∧ ‖z.2.1‖ < s}) =
      unitaryNormalMeasure n s Set.univ * unitaryHaar n S := by
  rw [← unitaryNormalMeasure_apply n s hS]
  simpa only [Measure.smul_apply, smul_eq_mul] using
    congrArg (fun μ : Measure (Matrix.unitaryGroup n ℂ) => μ S) (unitaryNormalMeasure_eq_smul n s)

/-- For s<=1/2 the fixed compact domain covers every Hermitian normal coordinate of norm <s. -/
theorem unitaryNormalMeasure_apply_of_le_half {s : ℝ} (hs : s ≤ 1 / 2)
    {S : Set (Matrix.unitaryGroup n ℂ)} (hS : MeasurableSet S) :
    unitaryNormalMeasure n s S = volume {y | ∃ U ∈ S, ∃ Q : Matrix n n ℂ,
      Q.IsHermitian ∧ ‖Q‖ < s ∧ matrixFrobeniusCoordinates n n ((U : Matrix n n ℂ) * (1 + Q)) = y} := by
  rw [unitaryNormalMeasure_apply n s hS]
  congr 1
  ext y
  constructor
  · rintro ⟨⟨U, Q⟩, h, he⟩
    exact ⟨U, h.1, Q.1, Q.2.1, h.2, he⟩
  · rintro ⟨U, hU, Q, hQ, hQs, he⟩
    exact ⟨(U, ⟨Q, hQ, hQs.le.trans hs⟩), ⟨hU, hQs⟩, he⟩

/-- The source's normal-volume/Haar identity, for the full Hermitian ball. -/
theorem normalVolume_eq_total_mul_haar {s : ℝ} (hs : s ≤ 1 / 2)
    {S : Set (Matrix.unitaryGroup n ℂ)} (hS : MeasurableSet S) :
    volume {y | ∃ U ∈ S, ∃ Q : Matrix n n ℂ, Q.IsHermitian ∧ ‖Q‖ < s ∧
      matrixFrobeniusCoordinates n n ((U : Matrix n n ℂ) * (1 + Q)) = y} =
      unitaryNormalMeasure n s Set.univ * unitaryHaar n S := by
  rw [← unitaryNormalMeasure_apply_of_le_half n hs hS]
  simpa only [Measure.smul_apply, smul_eq_mul] using
    congrArg (fun μ : Measure (Matrix.unitaryGroup n ℂ) => μ S) (unitaryNormalMeasure_eq_smul n s)

end NLQCLean

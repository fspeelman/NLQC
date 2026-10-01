import NLQCLean.Geometry.OperatorNormalEmbedding
import NLQCLean.Geometry.UnitaryNormalVolume

/-!
# The operator-normal image measure

Pull back ambient Euclidean volume through the
operator-normal embedding, restrict to `‖Q‖_F < s`, and project to the unitary. Left
invariance makes it its total mass times probability Haar, for every radius `s`; the image
over `S` lies in the open Frobenius `s`-tube. This repeats `UnitaryNormalMeasure` for the
operator-limited domain.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius ENNReal

variable (n : Type*) [Fintype n] [DecidableEq n]

def opNormalSlice (s : ℝ) : Set (OpNormalDomain n) := {z | ‖z.2.1‖ < s}

theorem measurableSet_opNormalSlice (s : ℝ) : MeasurableSet (opNormalSlice n s) := by
  have hc : Continuous (fun z : OpNormalDomain n => ‖z.2.1‖) := by fun_prop
  exact (isOpen_lt hc continuous_const).measurableSet

noncomputable def opNormalDomainVolume : Measure (OpNormalDomain n) :=
  volume.comap (opNormalEuclideanMap n)

theorem opNormalDomainVolume_apply {S : Set (OpNormalDomain n)} (hS : MeasurableSet S) :
    opNormalDomainVolume n S = volume (opNormalEuclideanMap n '' S) :=
  Measure.comap_apply _ (measurableEmbedding_opNormalEuclideanMap n).injective
    (fun _ h => (measurableEmbedding_opNormalEuclideanMap n).measurableSet_image.mpr h) volume hS

instance isFiniteMeasure_opNormalDomainVolume : IsFiniteMeasure (opNormalDomainVolume n) where
  measure_univ_lt_top := by
    rw [opNormalDomainVolume_apply n MeasurableSet.univ, Set.image_univ]
    exact (isCompact_range_opNormalEuclideanMap n).measure_lt_top

/-- The operator-normal image measure, for every real radius. -/
noncomputable def unitaryOpNormalMeasure (s : ℝ) : Measure (Matrix.unitaryGroup n ℂ) :=
  ((opNormalDomainVolume n).restrict (opNormalSlice n s)).map Prod.fst

instance isFiniteMeasure_unitaryOpNormalMeasure (s : ℝ) :
    IsFiniteMeasure (unitaryOpNormalMeasure n s) := by
  unfold unitaryOpNormalMeasure
  infer_instance

theorem unitaryOpNormalMeasure_apply (s : ℝ) {S : Set (Matrix.unitaryGroup n ℂ)}
    (hS : MeasurableSet S) :
    unitaryOpNormalMeasure n s S =
      volume (opNormalEuclideanMap n '' {z : OpNormalDomain n | z.1 ∈ S ∧ ‖z.2.1‖ < s}) := by
  rw [unitaryOpNormalMeasure, Measure.map_apply continuous_fst.measurable hS,
    Measure.restrict_apply (continuous_fst.measurable hS),
    opNormalDomainVolume_apply n
      ((continuous_fst.measurable hS).inter (measurableSet_opNormalSlice n s))]
  rfl

theorem opNormalImage_preimage_left_mul (s : ℝ) (U : Matrix.unitaryGroup n ℂ)
    (S : Set (Matrix.unitaryGroup n ℂ)) :
    opNormalEuclideanMap n '' {z : OpNormalDomain n | U * z.1 ∈ S ∧ ‖z.2.1‖ < s} =
      unitaryLeftEuclidean U ⁻¹'
        (opNormalEuclideanMap n '' {z : OpNormalDomain n | z.1 ∈ S ∧ ‖z.2.1‖ < s}) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(U * z.1, z.2), hz, opNormalEuclideanMap_left_mul U z⟩
  · rintro ⟨w, hw, he⟩
    refine ⟨(U⁻¹ * w.1, w.2), ⟨by simpa using hw.1, hw.2⟩, ?_⟩
    apply (unitaryLeftEuclidean U).injective
    rw [← opNormalEuclideanMap_left_mul]
    simpa using he

instance isMulLeftInvariant_unitaryOpNormalMeasure (s : ℝ) :
    (unitaryOpNormalMeasure n s).IsMulLeftInvariant := by
  apply (forall_measure_preimage_mul_iff _).mp
  intro U S hS
  have hpre : MeasurableSet ((fun V => U * V) ⁻¹' S) := (continuous_const_mul U).measurable hS
  rw [unitaryOpNormalMeasure_apply n s hpre, unitaryOpNormalMeasure_apply n s hS]
  change volume (opNormalEuclideanMap n '' {z : OpNormalDomain n | U * z.1 ∈ S ∧ ‖z.2.1‖ < s}) = _
  rw [opNormalImage_preimage_left_mul]
  apply (measurePreserving_unitaryLeftEuclidean U).measure_preimage
  apply MeasurableSet.nullMeasurableSet
  apply (measurableEmbedding_opNormalEuclideanMap n).measurableSet_image.mpr
  exact (continuous_fst.measurable hS).inter (measurableSet_opNormalSlice n s)

theorem unitaryOpNormalMeasure_eq_smul (s : ℝ) :
    unitaryOpNormalMeasure n s = unitaryOpNormalMeasure n s Set.univ • unitaryHaar n :=
  unitary_invariant_measure_eq_smul n (unitaryOpNormalMeasure n s)

theorem opNormalImageVolume_eq_total_mul_haar (s : ℝ) {S : Set (Matrix.unitaryGroup n ℂ)}
    (hS : MeasurableSet S) :
    volume (opNormalEuclideanMap n '' {z : OpNormalDomain n | z.1 ∈ S ∧ ‖z.2.1‖ < s}) =
      unitaryOpNormalMeasure n s Set.univ * unitaryHaar n S := by
  rw [← unitaryOpNormalMeasure_apply n s hS]
  simpa only [Measure.smul_apply, smul_eq_mul] using
    congrArg (fun μ : Measure (Matrix.unitaryGroup n ℂ) => μ S) (unitaryOpNormalMeasure_eq_smul n s)

theorem opNormalImage_subset_unitaryFrobeniusTube (s : ℝ) (S : Set (Matrix.unitaryGroup n ℂ)) :
    opNormalEuclideanMap n '' {z : OpNormalDomain n | z.1 ∈ S ∧ ‖z.2.1‖ < s} ⊆
      unitaryFrobeniusTube n s S := by
  rintro y ⟨z, hz, rfl⟩
  refine ⟨z.1, hz.1, ?_⟩
  rw [dist_eq_norm, norm_opNormalEuclideanMap_sub]
  exact hz.2

/-- Tube comparison for the operator-normal measure, before the total-mass bound. -/
theorem unitaryOpNormalMeasure_total_mul_haar_le_tube (s : ℝ) {S : Set (Matrix.unitaryGroup n ℂ)}
    (hS : MeasurableSet S) :
    unitaryOpNormalMeasure n s Set.univ * unitaryHaar n S ≤ volume (unitaryFrobeniusTube n s S) := by
  rw [← opNormalImageVolume_eq_total_mul_haar n s hS]
  exact measure_mono (opNormalImage_subset_unitaryFrobeniusTube n s S)

end NLQCLean

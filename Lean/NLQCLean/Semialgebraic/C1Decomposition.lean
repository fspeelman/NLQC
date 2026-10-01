/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.Projection
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Analytic consequences of the audited smooth cubes

The C1 parametrizations give local Lipschitz control,
Hausdorff dimension bounds and lower-dimensional nullity. These conclusions
use no external dimension or volume theorem.
-/

section

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace NLQCLean

theorem isOpen_openUnitCube (d : ℕ) : IsOpen (openUnitCube d) := by
  change IsOpen {x : RealEuclidean d | ∀ i, x i ∈ Ioo (0 : ℝ) 1}
  rw [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_Ioo.preimage
    (show Continuous (fun x : RealEuclidean d => x i) by fun_prop)

theorem convex_openUnitCube (d : ℕ) : Convex ℝ (openUnitCube d) := by
  intro x hx y hy a b ha hb hab i
  change 0 < a * x i + b * y i ∧ a * x i + b * y i < 1
  exact convex_Ioo (0 : ℝ) 1 (hx i) (hy i) ha hb hab

theorem openUnitCube_nonempty (d : ℕ) : (openUnitCube d).Nonempty := by
  refine ⟨WithLp.toLp 2 (fun _ => (1 / 2 : ℝ)), ?_⟩
  intro i
  norm_num

@[fun_prop] theorem contDiff_coordinateProjection {n k : ℕ} (I : Fin k → Fin n) :
    ContDiff ℝ 1 (coordinateProjection I) := by
  apply (contDiff_piLp 2).2
  intro j
  exact contDiff_piLp_apply (p := 2) (i := I j)

theorem volume_eq_zero_of_dimH_lt {n : ℕ} {S : Set (RealEuclidean n)}
    (h : dimH S < n) : volume S = 0 := by
  have hNull : (Measure.hausdorffMeasure (n : ℝ) : Measure (RealEuclidean n)) S = 0 :=
    hausdorffMeasure_of_dimH_lt (d := (n : ℝ≥0)) (by simpa using h)
  have hHaar : (Measure.hausdorffMeasure (n : ℝ) : Measure (RealEuclidean n)) =
      Measure.hausdorffMeasure (Module.finrank ℝ (RealEuclidean n)) := by simp
  rw [hHaar] at hNull
  exact Measure.absolutelyContinuous_isAddHaarMeasure
    (volume : Measure (RealEuclidean n))
    (Measure.hausdorffMeasure (Module.finrank ℝ (RealEuclidean n))) hNull

theorem contDiffOn_openUnitCube_dimH_image_le {d n : ℕ}
    {φ : RealEuclidean d → RealEuclidean n}
    (hφ : ContDiffOn ℝ 1 φ (openUnitCube d)) :
    dimH (φ '' openUnitCube d) ≤ d := by
  calc
    _ ≤ dimH (openUnitCube d) := hφ.dimH_image_le (convex_openUnitCube d) Subset.rfl
    _ ≤ dimH (univ : Set (RealEuclidean d)) := dimH_mono (subset_univ _)
    _ = d := by simp [Real.dimH_univ_eq_finrank]

theorem SemialgebraicSmoothCube.exists_locallyLipschitz_parametrization
    {n d : ℕ} {C : Set (RealEuclidean n)} (hC : SemialgebraicSmoothCube C d) :
    ∃ φ : RealEuclidean d → RealEuclidean n,
      φ '' openUnitCube d = C ∧ LocallyLipschitzOn (openUnitCube d) φ := by
  obtain ⟨_, _, _, φ, hφ, _, hdiff, _⟩ := hC
  exact ⟨φ, hφ, hdiff.locallyLipschitzOn (convex_openUnitCube d)⟩

theorem SemialgebraicSmoothCube.dimH_le {n d : ℕ} {C : Set (RealEuclidean n)}
    (hC : SemialgebraicSmoothCube C d) : dimH C ≤ d := by
  obtain ⟨_, _, _, φ, rfl, _, hdiff, _⟩ := hC
  exact contDiffOn_openUnitCube_dimH_image_le hdiff

theorem SemialgebraicSmoothCube.dimH_image_le {n d m : ℕ}
    {C : Set (RealEuclidean n)} (hC : SemialgebraicSmoothCube C d)
    {f : RealEuclidean n → RealEuclidean m} (hf : ContDiffOn ℝ 1 f C) :
    dimH (f '' C) ≤ d := by
  obtain ⟨_, _, _, φ, hφ, _, hdiff, _⟩ := hC
  rw [← hφ, ← image_comp]
  exact contDiffOn_openUnitCube_dimH_image_le
    (hf.comp hdiff (fun x hx => hφ ▸ mem_image_of_mem φ hx))

theorem SemialgebraicSmoothCube.coordinateInteriorDimension_le {n d : ℕ}
    {C : Set (RealEuclidean n)} (hC : SemialgebraicSmoothCube C d) :
    coordinateInteriorDimension C ≤ d := by
  classical
  apply Finset.sup_le
  intro k hk
  obtain ⟨I, _, hI⟩ := (Finset.mem_filter.mp hk).2
  have h := hC.dimH_image_le (contDiff_coordinateProjection I).contDiffOn
  rw [Real.dimH_of_nonempty_interior hI] at h
  simpa using h

theorem SemialgebraicSmoothCube.volume_eq_zero {n d : ℕ}
    {C : Set (RealEuclidean n)} (hC : SemialgebraicSmoothCube C d) (hd : d < n) :
    volume C = 0 :=
  volume_eq_zero_of_dimH_lt (hC.dimH_le.trans_lt (by exact_mod_cast hd))

theorem SemialgebraicSmoothCube.volume_image_eq_zero {n d m : ℕ}
    {C : Set (RealEuclidean n)} (hC : SemialgebraicSmoothCube C d)
    {f : RealEuclidean n → RealEuclidean m} (hf : ContDiffOn ℝ 1 f C) (hd : d < m) :
    volume (f '' C) = 0 :=
  volume_eq_zero_of_dimH_lt ((hC.dimH_image_le hf).trans_lt (by exact_mod_cast hd))

theorem SemialgebraicSmoothCube.finite_of_dimension_zero {n : ℕ}
    {C : Set (RealEuclidean n)} (hC : SemialgebraicSmoothCube C 0) : C.Finite := by
  obtain ⟨_, _, _, φ, rfl, _⟩ := hC
  exact (Set.toFinite (openUnitCube 0)).image φ

theorem SmoothCubeDecomposition.piece_subset {n : ℕ} {S : Set (RealEuclidean n)}
    (P : SmoothCubeDecomposition S) (i : Fin P.count) : P.piece i ⊆ S := by
  exact (subset_iUnion P.piece i).trans_eq P.covers

theorem SmoothCubeDecomposition.dimH_le {n d : ℕ} {S : Set (RealEuclidean n)}
    (P : SmoothCubeDecomposition S) (hd : ∀ i, P.dimension i ≤ d) : dimH S ≤ d := by
  rw [← P.covers, dimH_iUnion]
  exact iSup_le fun i => (P.smoothCube i).dimH_le.trans (by exact_mod_cast hd i)

theorem SmoothCubeDecomposition.dimH_image_le {n m d : ℕ}
    {S : Set (RealEuclidean n)} (P : SmoothCubeDecomposition S)
    {f : RealEuclidean n → RealEuclidean m} (hf : ContDiffOn ℝ 1 f S)
    (hd : ∀ i, P.dimension i ≤ d) : dimH (f '' S) ≤ d := by
  rw [← P.covers, image_iUnion, dimH_iUnion]
  exact iSup_le fun i =>
    ((P.smoothCube i).dimH_image_le (hf.mono (P.piece_subset i))).trans
      (by exact_mod_cast hd i)

theorem SmoothCubeDecomposition.coordinateInteriorDimension_le {n d : ℕ}
    {S : Set (RealEuclidean n)} (P : SmoothCubeDecomposition S)
    (hd : ∀ i, P.dimension i ≤ d) : coordinateInteriorDimension S ≤ d := by
  classical
  apply Finset.sup_le
  intro k hk
  obtain ⟨I, _, hI⟩ := (Finset.mem_filter.mp hk).2
  have h := P.dimH_image_le (contDiff_coordinateProjection I).contDiffOn hd
  rw [Real.dimH_of_nonempty_interior hI] at h
  simpa using h

theorem SmoothCubeDecomposition.volume_image_eq_zero {n m : ℕ}
    {S : Set (RealEuclidean n)} (P : SmoothCubeDecomposition S)
    {f : RealEuclidean n → RealEuclidean m} (hf : ContDiffOn ℝ 1 f S)
    (hd : ∀ i, P.dimension i < m) : volume (f '' S) = 0 := by
  rw [← P.covers, image_iUnion]
  exact measure_iUnion_null fun i => (P.smoothCube i).volume_image_eq_zero
    (hf.mono (P.piece_subset i)) (hd i)

theorem SmoothCubeDecomposition.finite_of_dimensions_zero {n : ℕ}
    {S : Set (RealEuclidean n)} (P : SmoothCubeDecomposition S)
    (hd : ∀ i, P.dimension i = 0) : S.Finite := by
  rw [← P.covers]
  apply Set.finite_iUnion
  intro i
  exact (hd i ▸ P.smoothCube i).finite_of_dimension_zero

end NLQCLean
end

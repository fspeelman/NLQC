/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.Dimension
import NLQCLean.Semialgebraic.ParametricFormat

/-!
# Finite fibers outside an explicit null set

Positive-dimensional nonempty fiber loci satisfy the audited
additive fiber-dimension inequality. Their finite union is semialgebraic and null
when source dimension is at most target dimension. Smooth stratification then makes all
remaining fibers finite. No exceptional-set or finite-fiber premise is added.
-/

section

open Set MeasureTheory

namespace NLQCLean

theorem SemialgebraicMapOn.image (hProjection : SemialgebraicProjectionTheorem)
    {n m : ℕ} {A : Set (RealEuclidean n)} {f : RealEuclidean n → RealEuclidean m}
    (hf : SemialgebraicMapOn A f) : Semialgebraic (f '' A) := by
  have h := hf.last_projection hProjection
  simpa only [image_image, coordinateProjection_pair_right] using h

/-- Fixing the output coordinate is polynomial substitution in the actual
graph. Thus fiber semialgebraicity itself needs no projection theorem. -/
theorem SemialgebraicMapOn.fiber {n m : ℕ} {A : Set (RealEuclidean n)}
    {f : RealEuclidean n → RealEuclidean m} (hf : SemialgebraicMapOn A f)
    (y : RealEuclidean m) : Semialgebraic (semialgebraicMapFiber A f y) := by
  let q : Fin (n + m) → MvPolynomial (Fin n) ℝ :=
    Fin.append MvPolynomial.X (fun j => MvPolynomial.C (y j))
  have hq (x : RealEuclidean n) : PolynomialSignDNF.polynomialMap q x =
      euclideanPair x y := by
    ext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [PolynomialSignDNF.polynomialMap, q]
  have h := hf.polynomial_preimage q
  convert h using 1
  ext x
  simp only [mem_preimage, hq, mem_image, semialgebraicMapFiber, mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hxy⟩
    exact ⟨x, hx, by rw [hxy]⟩
  · rintro ⟨z, hz, hzx⟩
    have hzx' : z = x := by
      simpa using congrArg (coordinateProjection (Fin.castAdd m)) hzx
    subst z
    exact ⟨hz, by simpa using congrArg (coordinateProjection (Fin.natAdd n)) hzx⟩

theorem Semialgebraic.coordinate_graph {n m : ℕ} {A : Set (RealEuclidean n)}
    (hA : Semialgebraic A) (I : Fin m → Fin n) :
    SemialgebraicMapOn A (coordinateProjection I) := by
  convert hA.polynomial_graph (fun j => MvPolynomial.X (I j)) using 1
  funext x
  ext j
  simp [PolynomialSignDNF.polynomialMap]

def positiveDimensionalFiberBase {n m : ℕ} (A : Set (RealEuclidean n))
    (f : RealEuclidean n → RealEuclidean m) : Set (RealEuclidean m) :=
  {y | 0 < coordinateInteriorDimension (semialgebraicMapFiber A f y)}

theorem positiveDimensionalFiberBase_eq_iUnion {n m : ℕ}
    (A : Set (RealEuclidean n)) (f : RealEuclidean n → RealEuclidean m) :
    positiveDimensionalFiberBase A f = ⋃ r : Fin (n + 1),
      if 0 < r.val then nonemptyFiberDimensionLocus A f r.val else ∅ := by
  ext y
  simp only [positiveDimensionalFiberBase, mem_ofPred_eq, mem_iUnion]
  constructor
  · intro hy
    refine ⟨⟨coordinateInteriorDimension (semialgebraicMapFiber A f y),
      Nat.lt_succ_of_le (coordinateInteriorDimension_le _)⟩, ?_⟩
    simp only [if_pos hy, nonemptyFiberDimensionLocus, mem_ofPred_eq, and_true]
    by_contra hempty
    have hzero := Set.not_nonempty_iff_eq_empty.mp hempty
    simp [hzero] at hy
  · rintro ⟨r, hr⟩
    split_ifs at hr with hpos
    · exact hr.2 ▸ hpos
    · exact False.elim hr

theorem semialgebraic_positiveDimensionalFiberBase
    (hFiber : SemialgebraicDimensionFiberTheorem)
    {n m : ℕ} {A : Set (RealEuclidean n)} (hA : Semialgebraic A)
    {f : RealEuclidean n → RealEuclidean m} (hcont : ContinuousOn f A)
    (hmap : SemialgebraicMapOn A f) : Semialgebraic (positiveDimensionalFiberBase A f) := by
  rw [positiveDimensionalFiberBase_eq_iUnion]
  apply Semialgebraic.iUnion
  intro r
  split_ifs
  · exact (hFiber n m A hA f hcont hmap r.val).1
  · exact Semialgebraic.empty

theorem volume_nonemptyFiberDimensionLocus_eq_zero
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hFiber : SemialgebraicDimensionFiberTheorem)
    {n m : ℕ} {A : Set (RealEuclidean n)} (hA : Semialgebraic A)
    {f : RealEuclidean n → RealEuclidean m} (hcont : ContinuousOn f A)
    (hmap : SemialgebraicMapOn A f) (hd : coordinateInteriorDimension A ≤ m)
    {r : ℕ} (hr : 0 < r) : volume (nonemptyFiberDimensionLocus A f r) = 0 := by
  obtain ⟨hsem, hbound⟩ := hFiber n m A hA f hcont hmap r
  by_cases hne : (nonemptyFiberDimensionLocus A f r).Nonempty
  · apply hsem.volume_eq_zero_of_dimension_lt hStratification
    have := hbound hne
    omega
  · simp [Set.not_nonempty_iff_eq_empty.mp hne]

theorem volume_positiveDimensionalFiberBase_eq_zero
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hFiber : SemialgebraicDimensionFiberTheorem)
    {n m : ℕ} {A : Set (RealEuclidean n)} (hA : Semialgebraic A)
    {f : RealEuclidean n → RealEuclidean m} (hcont : ContinuousOn f A)
    (hmap : SemialgebraicMapOn A f) (hd : coordinateInteriorDimension A ≤ m) :
    volume (positiveDimensionalFiberBase A f) = 0 := by
  rw [positiveDimensionalFiberBase_eq_iUnion]
  apply measure_iUnion_null
  intro r
  split_ifs with hr
  · exact volume_nonemptyFiberDimensionLocus_eq_zero hStratification hFiber hA hcont hmap hd hr
  · exact measure_empty

theorem ae_finite_semialgebraicMapFiber
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hFiber : SemialgebraicDimensionFiberTheorem)
    {n m : ℕ} {A : Set (RealEuclidean n)} (hA : Semialgebraic A)
    {f : RealEuclidean n → RealEuclidean m} (hcont : ContinuousOn f A)
    (hmap : SemialgebraicMapOn A f) (hd : coordinateInteriorDimension A ≤ m) :
    ∀ᵐ y, (semialgebraicMapFiber A f y).Finite := by
  have hae : ∀ᵐ y, y ∉ positiveDimensionalFiberBase A f := by
    simpa only [ae_iff, not_not, ofPred_mem_eq] using
      volume_positiveDimensionalFiberBase_eq_zero hStratification hFiber hA hcont hmap hd
  filter_upwards [hae] with y hy
  apply (hmap.fiber y).finite_of_dimension_zero hStratification
  change ¬ 0 < coordinateInteriorDimension (semialgebraicMapFiber A f y) at hy
  omega

theorem ae_finite_coordinateFiber
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hFiber : SemialgebraicDimensionFiberTheorem)
    {n m : ℕ} {A : Set (RealEuclidean n)} (hA : Semialgebraic A)
    (I : Fin m → Fin n) (hd : coordinateInteriorDimension A ≤ m) :
    ∀ᵐ y, (semialgebraicMapFiber A (coordinateProjection I) y).Finite :=
  ae_finite_semialgebraicMapFiber hStratification hFiber hA
    (continuous_coordinateProjection I).continuousOn (hA.coordinate_graph I) hd

end NLQCLean
end

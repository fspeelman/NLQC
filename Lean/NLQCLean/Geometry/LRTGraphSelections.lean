/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Geometry.PolynomialGraphFormat
import NLQCLean.Semialgebraic.AffineSlices
import NLQCLean.Semialgebraic.CoordinateDimensionProjection
import NLQCLean.External.LRT44
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# LRT selections of the polynomial graph

Coordinate contraction, compactness and nonemptiness are
derived from the audited LRT conclusions, with one positive format cap
chosen before every dimension and coefficient.
-/

section

open Set Filter MeasureTheory Metric
open scoped Topology BigOperators ENNReal

namespace NLQCLean

theorem norm_coordinateProjection_le {n k : ℕ} (I : Fin k → Fin n)
    (hI : Function.Injective I) (x : RealEuclidean n) : ‖coordinateProjection I x‖ ≤ ‖x‖ := by
  classical
  have hsum : ∑ j : Fin k, (x (I j)) ^ 2 ≤ ∑ i : Fin n, (x i) ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.univ.image I, (x i) ^ 2 := (Finset.sum_image hI.injOn).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => sq_nonneg _)
  have hx := EuclideanSpace.real_norm_sq_eq x
  have hproj := EuclideanSpace.real_norm_sq_eq (coordinateProjection I x)
  simp only [coordinateProjection_apply] at hproj
  nlinarith [norm_nonneg x, norm_nonneg (coordinateProjection I x)]

theorem dist_coordinateProjection_le {n k : ℕ} (I : Fin k → Fin n)
    (hI : Function.Injective I) (x y : RealEuclidean n) :
    dist (coordinateProjection I x) (coordinateProjection I y) ≤ dist x y := by
  have h := norm_coordinateProjection_le I hI (x - y)
  have heq : coordinateProjection I (x - y) = coordinateProjection I x - coordinateProjection I y := by
    ext j
    rfl
  simpa only [heq, dist_eq_norm] using h

theorem isCompact_of_subset_closedEuclideanNeighborhood {n : ℕ}
    {S A : Set (RealEuclidean n)} {ε : ℝ} (hS : IsCompact S) (hA : IsClosed A)
    (hAS : A ⊆ closedEuclideanNeighborhood S ε) : IsCompact A := by
  obtain ⟨R, hR⟩ := hS.isBounded.exists_norm_le
  apply (isCompact_closedBall (0 : RealEuclidean n) (R + ε)).of_isClosed_subset hA
  intro x hx
  obtain ⟨s, hs, hxs⟩ := hAS hx
  simp only [mem_closedBall, dist_zero_right]
  calc
    ‖x‖ ≤ ‖x - s‖ + ‖s‖ := norm_le_norm_sub_add x s
    _ ≤ ε + R := add_le_add hxs (hR s hs)
    _ = R + ε := add_comm _ _

theorem LRTTheorem44.exists_compact_choices (hLRT : LRTTheorem44) (c : ℕ) :
    ∃ κ : ℕ, 1 ≤ κ ∧ ∀ n l D : ℕ, ∀ hln : l ≤ n, 1 ≤ l →
      ∀ S : Set (RealEuclidean n), IsCompact S → S.Nonempty → HasSemialgebraicFormat S c D →
        ∀ ε : ℝ, 0 < ε → ∃ A : Set (RealEuclidean n),
          IsCompact A ∧ A.Nonempty ∧ coordinateInteriorDimension A ≤ l ∧
          A ⊆ closedEuclideanNeighborhood S ε ∧
          hausdorffEDist (lastCoordinateProjection hln '' A) (lastCoordinateProjection hln '' S) ≤
            ENNReal.ofReal ε ∧ HasSemialgebraicFormat A κ (κ * D) := by
  obtain ⟨κ, hκ⟩ := hLRT c
  refine ⟨κ + 1, by omega, ?_⟩
  intro n l D hln hl S hS hne hfmt ε hε
  obtain ⟨A, hAc, hAd, hAS, hAH, hAF⟩ := hκ n l D hln hl S hS hne hfmt ε hε
  have hAne : A.Nonempty := by
    by_contra h
    have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [he, image_empty, hausdorffEDist_comm,
      hausdorffEDist_empty (hne.image (lastCoordinateProjection hln))] at hAH
    exact (not_le_of_gt ENNReal.ofReal_lt_top) hAH
  exact ⟨A, isCompact_of_subset_closedEuclideanNeighborhood hS hAc hAS,
    hAne, hAd, hAS, hAH, hAF.mono (by omega) (Nat.mul_le_mul_right D (by omega))⟩

@[simp] theorem lastCoordinateProjection_add (a m : ℕ) :
    lastCoordinateProjection (show m ≤ a + m by omega) = coordinateProjection (Fin.natAdd a) := by
  funext x
  ext j
  change x ⟨a + m - m + j.val, _⟩ = x (Fin.natAdd a j)
  exact congrArg (fun i : Fin (a + m) => x i) (Fin.ext (by simp))

@[simp] theorem polynomialGraphSource_first_projection {a m : ℕ}
    (F : PolynomialBasicClosedFormat a) (p : BoundedPolynomialMap a m) :
    coordinateProjection (Fin.castAdd m) '' polynomialGraphSource F p = F.source := by
  simp [polynomialGraphSource, image_image, coordinateProjection_pair_left]

@[simp] theorem polynomialGraphSource_last_projection {a m : ℕ}
    (F : PolynomialBasicClosedFormat a) (p : BoundedPolynomialMap a m) :
    coordinateProjection (Fin.natAdd a) '' polynomialGraphSource F p = p.eval '' F.source := by
  simp only [polynomialGraphSource, image_image, coordinateProjection_pair_right]

noncomputable def lrtTolerance (j : ℕ) : ℝ := 1 / (j + 2 : ℝ)

theorem lrtTolerance_pos (j : ℕ) : 0 < lrtTolerance j := by unfold lrtTolerance; positivity

theorem lrtTolerance_le_one (j : ℕ) : lrtTolerance j ≤ 1 := by
  unfold lrtTolerance
  apply (div_le_one (by positivity)).mpr
  have := Nat.cast_nonneg (α := ℝ) j
  linarith

theorem tendsto_lrtTolerance : Tendsto lrtTolerance atTop (𝓝 0) := by
  change Tendsto (fun j : ℕ => (1 : ℝ) / (j + 2)) atTop (𝓝 0)
  simpa only [one_div, Function.comp_def] using
    (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ (2 : ℝ) tendsto_natCast_atTop_atTop))

structure PolynomialGraphSelections {a m : ℕ}
    (F : PolynomialBasicClosedFormat a) (p : BoundedPolynomialMap a m) (κ : ℕ) where
  selection : ℕ → Set (RealEuclidean (a + m))
  compact : ∀ j, IsCompact (selection j)
  nonempty : ∀ j, (selection j).Nonempty
  format : ∀ j, HasSemialgebraicFormat (selection j) κ (κ * 200)
  dimension : ∀ j, coordinateInteriorDimension (selection j) ≤ m
  proximity : ∀ j, selection j ⊆ closedEuclideanNeighborhood (polynomialGraphSource F p) (lrtTolerance j)
  outputApprox : ∀ j, hausdorffEDist (coordinateProjection (Fin.natAdd a) '' selection j)
    (p.eval '' F.source) ≤ ENNReal.ofReal (lrtTolerance j)
  sourceBound : ∀ j, coordinateProjection (Fin.castAdd m) '' selection j ⊆ closedBall 0 4
  sourceDimension : ∀ j, coordinateInteriorDimension (coordinateProjection (Fin.castAdd m) '' selection j) ≤ m
  sourceSemialgebraic : ∀ j, Semialgebraic (coordinateProjection (Fin.castAdd m) '' selection j)

theorem exists_polynomialGraphSelections (hLRT : LRTTheorem44)
    (hProjection : SemialgebraicProjectionTheorem) :
    ∃ κ : ℕ, 1 ≤ κ ∧ ∀ a m : ℕ, 1 ≤ m →
      ∀ F : PolynomialBasicClosedFormat a, ∀ p : BoundedPolynomialMap a m,
        IsCompact F.source → F.source.Nonempty → F.source ⊆ closedBall 0 3 →
          Nonempty (PolynomialGraphSelections F p κ) := by
  obtain ⟨κ, hκpos, hκ⟩ := hLRT.exists_compact_choices lrtGraphFormatBudget
  refine ⟨κ, hκpos, ?_⟩
  intro a m hm F p hF hFne hFbound
  have hchoices (j : ℕ) := hκ (a + m) m 200 (by omega) hm (polynomialGraphSource F p)
    (polynomialGraphSource_isCompact F p hF) (hFne.image _)
    (polynomialGraphSource_hasFormat F p) (lrtTolerance j) (lrtTolerance_pos j)
  choose A hAc hAne hAd hAS hAH hAF using hchoices
  have hfirst : Function.Injective (Fin.castAdd m : Fin a → Fin (a + m)) :=
    Fin.castAdd_injective _ _
  refine ⟨{
    selection := A
    compact := hAc
    nonempty := hAne
    format := hAF
    dimension := hAd
    proximity := hAS
    outputApprox := ?_
    sourceBound := ?_
    sourceDimension := ?_
    sourceSemialgebraic := ?_ }⟩
  · intro j
    simpa only [lastCoordinateProjection_add, polynomialGraphSource_last_projection] using hAH j
  · rintro j x ⟨z, hz, rfl⟩
    obtain ⟨_, ⟨s, hs, rfl⟩, hzs⟩ := hAS j hz
    have hdist := dist_coordinateProjection_le (Fin.castAdd m) hfirst z (euclideanPair s (p.eval s))
    simp only [coordinateProjection_pair_left, dist_eq_norm] at hdist
    have hsnorm : ‖s‖ ≤ 3 := by simpa only [mem_closedBall, dist_zero_right] using hFbound hs
    simp only [mem_closedBall, dist_zero_right]
    have hnorm := norm_le_norm_sub_add (coordinateProjection (Fin.castAdd m) z) s
    have ht := lrtTolerance_le_one j
    linarith
  · intro j
    exact (coordinateInteriorDimension_image_coordinateProjection_le _ hfirst (A j)).trans (hAd j)
  · intro j
    exact ((hAF j).semialgebraic.coordinate_graph _).image hProjection

namespace PolynomialGraphSelections

variable {a m κ : ℕ} {F : PolynomialBasicClosedFormat a} {p : BoundedPolynomialMap a m}
  (P : PolynomialGraphSelections F p κ)

def source (j : ℕ) : Set (RealEuclidean a) :=
  coordinateProjection (Fin.castAdd m) '' P.selection j

theorem source_isCompact (j : ℕ) : IsCompact (P.source j) :=
  (P.compact j).image (continuous_coordinateProjection _)

theorem source_nonempty (j : ℕ) : (P.source j).Nonempty := (P.nonempty j).image _

theorem source_proximity (j : ℕ) : P.source j ⊆ closedEuclideanNeighborhood F.source (lrtTolerance j) := by
  rintro x ⟨z, hz, rfl⟩
  obtain ⟨_, ⟨s, hs, rfl⟩, hzs⟩ := P.proximity j hz
  refine ⟨s, hs, ?_⟩
  have h := dist_coordinateProjection_le (Fin.castAdd m) (Fin.castAdd_injective _ _) z
    (euclideanPair s (p.eval s))
  simpa only [coordinateProjection_pair_left, dist_eq_norm] using h.trans hzs

theorem finite_card_connectedComponents_affineSlice
    (hComponents : SemialgebraicComponentBoundTheorem) (hκ : 1 ≤ κ)
    (j : ℕ) {r k : ℕ} (I : Fin r → Fin a) (M : Fin k → Fin r → ℝ) (b : Fin k → ℝ) :
    Finite (ConnectedComponents ↥(P.source j ∩ affineCoordinateSlice I M b)) ∧
      Nat.card (ConnectedComponents ↥(P.source j ∩ affineCoordinateSlice I M b)) ≤
        componentFormatBase (2 * κ) (max (κ * 200) 2) ^ (a + m) :=
  (P.format j).finite_card_connectedComponents_projected_affineSlice hComponents hκ
    (Fin.castAdd m) I M b

theorem ae_card_coordinateFiber_le
    (hComponents : SemialgebraicComponentBoundTheorem)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hFiber : SemialgebraicDimensionFiberTheorem) (hκ : 1 ≤ κ)
    (j : ℕ) (I : Fin m → Fin a) :
    ∀ᵐ y, (semialgebraicMapFiber (P.source j) (coordinateProjection I) y).Finite ∧
      Nat.card (semialgebraicMapFiber (P.source j) (coordinateProjection I) y) ≤
        componentFormatBase (2 * κ) (max (κ * 200) 2) ^ (a + m) :=
  (P.format j).ae_card_projected_coordinateFiber_le hComponents hProjection hStratification hFiber
    hκ (Fin.castAdd m) I (P.sourceDimension j)

end PolynomialGraphSelections

end NLQCLean
end

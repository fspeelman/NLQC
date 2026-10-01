/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.CoordinateMaps

/-!
# Coordinate-interior dimension

The dimension is the largest number of
coordinate axes whose projection has nonempty interior. Empty sets have
natural-number dimension zero. This definition makes sense for all sets;
its correspondence with semialgebraic smooth-cell dimension is proved separately.
-/

section

namespace NLQCLean

/-- Some injective selection of k axes gives a projection with interior. -/
def HasCoordinateInterior {n : ℕ} (S : Set (RealEuclidean n)) (k : ℕ) : Prop :=
  ∃ I : Fin k → Fin n, Function.Injective I ∧
    (interior (coordinateProjection I '' S)).Nonempty

/-- The coordinate-interior dimension, with zero as the empty-set convention.
It contains no smooth decomposition, nullity or fiber-dimension premise. -/
noncomputable def coordinateInteriorDimension {n : ℕ} (S : Set (RealEuclidean n)) : ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter (HasCoordinateInterior S)).sup id

theorem coordinateInteriorDimension_le {n : ℕ} (S : Set (RealEuclidean n)) :
    coordinateInteriorDimension S ≤ n := by
  classical
  apply Finset.sup_le
  intro k hk
  have := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  simpa using Nat.le_of_lt_succ this

@[simp] theorem coordinateInteriorDimension_empty (n : ℕ) :
    coordinateInteriorDimension (∅ : Set (RealEuclidean n)) = 0 := by
  simp [coordinateInteriorDimension, HasCoordinateInterior]

theorem HasCoordinateInterior.mono {n k : ℕ} {S T : Set (RealEuclidean n)}
    (h : HasCoordinateInterior S k) (hST : S ⊆ T) : HasCoordinateInterior T k := by
  obtain ⟨I, hI, hx⟩ := h
  exact ⟨I, hI, hx.mono (interior_mono (Set.image_mono hST))⟩

theorem le_coordinateInteriorDimension {n k : ℕ} {S : Set (RealEuclidean n)}
    (h : HasCoordinateInterior S k) : k ≤ coordinateInteriorDimension S := by
  classical
  have hkn : k ≤ n := by
    simpa using Fintype.card_le_of_injective _ h.choose_spec.1
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h⟩)

theorem coordinateInteriorDimension_mono {n : ℕ} {S T : Set (RealEuclidean n)}
    (hST : S ⊆ T) : coordinateInteriorDimension S ≤ coordinateInteriorDimension T := by
  classical
  apply Finset.sup_le
  intro k hk
  exact le_coordinateInteriorDimension ((Finset.mem_filter.mp hk).2.mono hST)

theorem coordinateInteriorDimension_eq_of_interior_nonempty {n : ℕ}
    {S : Set (RealEuclidean n)} (hS : (interior S).Nonempty) :
    coordinateInteriorDimension S = n := by
  apply le_antisymm (coordinateInteriorDimension_le S)
  apply le_coordinateInteriorDimension
  exact ⟨id, Function.injective_id, by simpa using hS⟩

@[simp] theorem coordinateInteriorDimension_univ (n : ℕ) :
    coordinateInteriorDimension (Set.univ : Set (RealEuclidean n)) = n :=
  coordinateInteriorDimension_eq_of_interior_nonempty (by simp)

end NLQCLean
end

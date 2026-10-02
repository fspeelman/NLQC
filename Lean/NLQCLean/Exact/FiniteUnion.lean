import NLQCLean.Exact.ExactBadDecomposition
import NLQCLean.Exact.ExactPurityAlgebraicity
import NLQCLean.Semialgebraic.Components
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# `lem:finiteunion`

Each architecture's strategy set has finitely many connected components
(`fact:components`, transported along a linear coordinate homeomorphism), and
`Bad` is the union, over architectures and these components, of the targets
implemented by each component.
-/

noncomputable section

namespace NLQCLean

open Set ExactWitnessCoordinates

/-- Connected components are carried along homeomorphisms; finitely many
components on the image give finitely many on the source. -/
theorem finite_connectedComponentIn_of_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (h : X ≃ₜ Y) {s : Set X}
    (hfin : {C | ∃ y ∈ h '' s, C = connectedComponentIn (h '' s) y}.Finite) :
    {C | ∃ x ∈ s, C = connectedComponentIn s x}.Finite := by
  refine (hfin.image fun C => h.symm '' C).subset ?_
  rintro C ⟨x, hx, rfl⟩
  refine ⟨connectedComponentIn (h '' s) (h x), ⟨h x, mem_image_of_mem h hx, rfl⟩, ?_⟩
  change h.symm '' connectedComponentIn (h '' s) (h x) = _
  rw [← h.image_connectedComponentIn hx]
  exact h.toEquiv.symm_image_image _

variable {d : ℕ}

/-- The connected components of one architecture's strategy set. -/
def strategyComponents (d : ℕ) (s : ForwardShape) :
    Set (Set (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × ShapeBlocks d s)) :=
  {C | ∃ z ∈ targetExactWitnessSet d s, C = connectedComponentIn (targetExactWitnessSet d s) z}

/-- **Finitely many components per architecture.** -/
theorem finite_strategyComponents (d : ℕ) (s : ForwardShape) : (strategyComponents d s).Finite := by
  let L : Blocks d s ≃ₗ[ℝ] RealEuclidean (coordinateCount d s) :=
    (coordinatesEquiv d s).trans (WithLp.linearEquiv 2 ℝ (Fin (coordinateCount d s) → ℝ)).symm
  let H := L.toContinuousLinearEquiv.toHomeomorph
  refine finite_connectedComponentIn_of_homeomorph H ?_
  have himage : H '' targetExactWitnessSet d s = exactWitnessCoordinateSet d s := by
    ext x
    simp only [mem_image, exactWitnessCoordinateSet, mem_ofPred_eq]
    constructor
    · rintro ⟨z, hz, rfl⟩
      convert hz
      simp [H, L]
    · intro hx
      refine ⟨_, hx, ?_⟩
      simp [H, L]
  rw [himage]
  exact (fact_components (rationalSemialgebraic_exactWitnessCoordinateSet d s).semialgebraic).1

/-- **`lem:finiteunion`.** `Bad` is the union, over architectures and the
finitely many connected components of each strategy set, of the targets
implemented by the component. -/
theorem exactUnitaryBad_eq_iUnion_strategyComponents [NeZero d] :
    exactUnitaryBad d = ⋃ s : ForwardShape, ⋃ C ∈ strategyComponents d s, Prod.fst '' C ∧
      ∀ s, (strategyComponents d s).Finite := by
  refine ⟨?_, finite_strategyComponents d⟩
  rw [exactUnitaryBad_eq_iUnion_components]
  refine iUnion_congr fun s => ?_
  ext U
  simp only [mem_iUnion, exists_prop, strategyComponents, mem_ofPred_eq]
  constructor
  · rintro ⟨z, hz, hU⟩
    exact ⟨_, ⟨z, hz, rfl⟩, hU⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, hU⟩
    exact ⟨z, hz, hU⟩

end NLQCLean

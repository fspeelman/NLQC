/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Topology.Connected.Clopen
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Separation.Connected

/-!
# Comparisons of connected-component counts

Continuous surjections and finite unions give surjections between
component quotients. Finiteness is proved before using natural counts.
No component-counting predicate or geometric external result is introduced.
-/

section

open Set
open scoped BigOperators

namespace NLQCLean

def connectedComponentsMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) : ConnectedComponents X → ConnectedComponents Y :=
  Quotient.map f fun x y (hxy : connectedComponent x = connectedComponent y) => by
    apply connectedComponent_eq_iff_mem.mpr
    exact hf.mapsTo_connectedComponent y (hxy ▸ mem_connectedComponent)

@[simp] theorem connectedComponentsMap_mk {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (hf : Continuous f) (x : X) :
    connectedComponentsMap f hf (ConnectedComponents.mk x) = ConnectedComponents.mk (f x) := rfl

theorem connectedComponentsMap_surjective {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f)
    (hs : Function.Surjective f) : Function.Surjective (connectedComponentsMap f hf) := by
  intro c
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨x, rfl⟩ := hs y
  exact ⟨ConnectedComponents.mk x, rfl⟩

theorem finite_card_connectedComponents_of_surjective {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f)
    (hs : Function.Surjective f) (hfin : Finite (ConnectedComponents X)) :
    Finite (ConnectedComponents Y) ∧
      Nat.card (ConnectedComponents Y) ≤ Nat.card (ConnectedComponents X) := by
  have := hfin
  have hsurj := connectedComponentsMap_surjective hf hs
  exact ⟨Finite.of_surjective _ hsurj, Nat.card_le_card_of_surjective _ hsurj⟩

def subsetToUnion {X ι : Type*} (S : ι → Set X) (i : ι) : S i → (⋃ j, S j) :=
  fun x => ⟨x, mem_iUnion.mpr ⟨i, x.property⟩⟩

@[fun_prop] theorem continuous_subsetToUnion {X ι : Type*} [TopologicalSpace X]
    (S : ι → Set X) (i : ι) : Continuous (subsetToUnion S i) := by
  exact continuous_subtype_val.subtype_mk _

def connectedComponentsUnionMap {X ι : Type*} [TopologicalSpace X]
    (S : ι → Set X) : (Σ i, ConnectedComponents (S i)) → ConnectedComponents (⋃ i, S i) :=
  fun p => connectedComponentsMap (subsetToUnion S p.1) (continuous_subsetToUnion S p.1) p.2

theorem connectedComponentsUnionMap_surjective {X ι : Type*} [TopologicalSpace X]
    (S : ι → Set X) : Function.Surjective (connectedComponentsUnionMap S) := by
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
  refine ⟨⟨i, ConnectedComponents.mk ⟨x.val, hi⟩⟩, ?_⟩
  rfl

theorem finite_card_connectedComponents_iUnion {X ι : Type*}
    [TopologicalSpace X] [Fintype ι] (S : ι → Set X)
    (hfin : ∀ i, Finite (ConnectedComponents (S i))) :
    Finite (ConnectedComponents (⋃ i, S i)) ∧
      Nat.card (ConnectedComponents (⋃ i, S i)) ≤ ∑ i, Nat.card (ConnectedComponents (S i)) := by
  have (i : ι) := hfin i
  have hsurj := connectedComponentsUnionMap_surjective S
  refine ⟨Finite.of_surjective _ hsurj, ?_⟩
  simpa only [Nat.card_sigma] using Nat.card_le_card_of_surjective _ hsurj

theorem finite_card_connectedComponents_image {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {f : X → Y}
    (hf : ContinuousOn f A) (hfin : Finite (ConnectedComponents A)) :
    Finite (ConnectedComponents (f '' A)) ∧
      Nat.card (ConnectedComponents (f '' A)) ≤ Nat.card (ConnectedComponents A) := by
  let F : A → (f '' A) := fun x => ⟨f x, mem_image_of_mem f x.property⟩
  have hF : Continuous F := hf.domRestrict.subtype_mk _
  have hsurj : Function.Surjective F := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  exact finite_card_connectedComponents_of_surjective hF hsurj hfin

/-- In a finite T1 space each component is a singleton. In
particular finite semialgebraic fibers have point count equal to b0. -/
theorem finite_card_connectedComponents_of_finite {X : Type*}
    [TopologicalSpace X] [T1Space X] (hfin : Finite X) :
    Finite (ConnectedComponents X) ∧ Nat.card (ConnectedComponents X) = Nat.card X := by
  have := hfin
  have hinj : Function.Injective (ConnectedComponents.mk : X → ConnectedComponents X) := by
    intro x y hxy
    simpa only [connectedComponent_eq_singleton, mem_singleton_iff] using
      ConnectedComponents.coe_eq_coe'.mp hxy
  exact ⟨Finite.of_surjective _ ConnectedComponents.surjective_coe,
    (Nat.card_congr (Equiv.ofBijective ConnectedComponents.mk
      ⟨hinj, ConnectedComponents.surjective_coe⟩)).symm⟩

end NLQCLean
end

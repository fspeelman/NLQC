import NLQCLean.Semialgebraic.CellDecomposition

/-!
# Connected components of semialgebraic sets (`fact:components`)

A semialgebraic set has finitely many connected components, each
semialgebraic: it is a finite union of semialgebraically path-connected
semialgebraic pieces, and each component is the union of the pieces meeting
it.
-/

noncomputable section

namespace NLQCLean

open Set

theorem SAOn.sUnion {ι : Type*} {𝒟 : Set (Set (ι → ℝ))} (hfin : 𝒟.Finite)
    (h : ∀ D ∈ 𝒟, SAOn D) : SAOn (⋃₀ 𝒟) :=
  (SAOn.finset_iUnion hfin.toFinset fun D hD => h D (hfin.mem_toFinset.mp hD)).congr fun x => by
    simp

/-- In a finite union of preconnected sets, each connected component is the
union of the pieces meeting it, and there are finitely many components. -/
theorem connectedComponentIn_eq_sUnion {X : Type*} [TopologicalSpace X] {S : Set X}
    {𝒟 : Set (Set X)} (hpc : ∀ D ∈ 𝒟, IsPreconnected D) (hS : S = ⋃₀ 𝒟) {x : X} (_hx : x ∈ S) :
    connectedComponentIn S x = ⋃₀ {D ∈ 𝒟 | (D ∩ connectedComponentIn S x).Nonempty} := by
  ext z
  constructor
  · intro hz
    have hzS := connectedComponentIn_subset S x hz
    rw [hS] at hzS
    obtain ⟨D, hD, hzD⟩ := hzS
    exact ⟨D, ⟨hD, z, hzD, hz⟩, hzD⟩
  · rintro ⟨D, ⟨hD, w, hwD, hw⟩, hzD⟩
    have hDS : D ⊆ S := hS ▸ subset_sUnion_of_mem hD
    have := (hpc D hD).subset_connectedComponentIn hwD hDS hzD
    rwa [← connectedComponentIn_eq hw] at this

theorem finite_connectedComponentIn {X : Type*} [TopologicalSpace X] {S : Set X}
    {𝒟 : Set (Set X)} (hfin : 𝒟.Finite) (hpc : ∀ D ∈ 𝒟, IsPreconnected D) (hS : S = ⋃₀ 𝒟) :
    {C | ∃ x ∈ S, C = connectedComponentIn S x}.Finite := by
  classical
  let f : Set X → Set X := fun D => if h : D.Nonempty then connectedComponentIn S h.some else ∅
  refine (hfin.image f).subset ?_
  rintro C ⟨x, hx, rfl⟩
  have hx' := hx
  rw [hS] at hx'
  obtain ⟨D, hD, hxD⟩ := hx'
  refine ⟨D, hD, ?_⟩
  have hne : D.Nonempty := ⟨x, hxD⟩
  have hDS : D ⊆ S := hS ▸ subset_sUnion_of_mem hD
  simp only [f, dite_eq_left hne]
  have hsub := (hpc D hD).subset_connectedComponentIn hxD hDS
  exact (connectedComponentIn_eq (hsub hne.some_mem)).symm

/-- **`fact:components` in coordinates.** -/
theorem SAOn.components {n : ℕ} {S : Set (Fin n → ℝ)} (hS : SAOn S) :
    {C | ∃ x ∈ S, C = connectedComponentIn S x}.Finite ∧
      ∀ x ∈ S, SAOn (connectedComponentIn S x) := by
  obtain ⟨𝒟, hfin, hprop, hSeq⟩ := exists_saPathConnected_decomposition n S hS
  have hpc : ∀ D ∈ 𝒟, IsPreconnected D := fun D hD => (hprop D hD).2.isPreconnected
  refine ⟨finite_connectedComponentIn hfin hpc hSeq, fun x hx => ?_⟩
  rw [connectedComponentIn_eq_sUnion hpc hSeq hx]
  exact SAOn.sUnion (hfin.subset fun D hD => hD.1) fun D hD => (hprop D hD.1).1

theorem semialgebraic_iff_saOn {n : ℕ} (S : Set (RealEuclidean n)) :
    Semialgebraic S ↔ SAOn ((WithLp.toLp 2) ⁻¹' S) := by
  rw [semialgebraic_iff_sadef, saOn_iff_sadef]

/-- **`fact:components`.** A semialgebraic subset of `ℝⁿ` has finitely many
connected components, and each of them is semialgebraic. -/
theorem fact_components {n : ℕ} {S : Set (RealEuclidean n)} (hS : Semialgebraic S) :
    {C | ∃ x ∈ S, C = connectedComponentIn S x}.Finite ∧
      ∀ x ∈ S, Semialgebraic (connectedComponentIn S x) := by
  obtain ⟨𝒟, hfin, hprop, hSeq⟩ :=
    exists_saPathConnected_decomposition n _ ((semialgebraic_iff_saOn S).mp hS)
  let 𝒟' : Set (Set (RealEuclidean n)) := (fun D => WithLp.ofLp ⁻¹' D) '' 𝒟
  have hpc : ∀ D ∈ 𝒟', IsPreconnected D := by
    rintro _ ⟨D, hD, rfl⟩
    have h := (hprop D hD).2.isPreconnected.image (WithLp.toLp 2)
      (PiLp.continuous_toLp 2 _).continuousOn
    convert h using 1
    ext z
    simp only [mem_preimage, mem_image]
    exact ⟨fun hz => ⟨_, hz, by simp⟩, by rintro ⟨w, hw, rfl⟩; simpa using hw⟩
  have hS' : S = ⋃₀ 𝒟' := by
    ext z
    have := congrArg (fun T => WithLp.ofLp z ∈ T) hSeq
    simp only [mem_preimage, WithLp.toLp_ofLp, eq_iff_iff] at this
    rw [this]
    simp [𝒟']
  refine ⟨finite_connectedComponentIn (hfin.image _) hpc hS', fun x hx => ?_⟩
  rw [connectedComponentIn_eq_sUnion hpc hS' hx, semialgebraic_iff_saOn]
  let 𝒟₀ := {D ∈ 𝒟 | (WithLp.ofLp ⁻¹' D ∩ connectedComponentIn S x).Nonempty}
  have h₀ : SAOn (⋃₀ 𝒟₀) :=
    SAOn.sUnion (hfin.subset fun D (hD : D ∈ 𝒟₀) => hD.1) fun D (hD : D ∈ 𝒟₀) => (hprop D hD.1).1
  refine h₀.congr fun g => ?_
  simp only [mem_sUnion, mem_preimage, mem_ofPred_eq, 𝒟', 𝒟₀, mem_image]
  constructor
  · rintro ⟨D, ⟨hD, hne⟩, hgD⟩
    exact ⟨_, ⟨⟨D, hD, rfl⟩, hne⟩, by simpa using hgD⟩
  · rintro ⟨_, ⟨⟨D, hD, rfl⟩, hne⟩, hgD⟩
    exact ⟨D, ⟨hD, hne⟩, by simpa using hgD⟩

end NLQCLean

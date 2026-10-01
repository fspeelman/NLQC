import NLQCLean.Models.ClassicalCommunication.CoherentConversion

/-!
# Common-map finite mixed resources for classical instruments

Only the resource varies between components. Both actual instruments and
all outcome-dependent decoders are shared. A real-linear channel score is
the convex average of component scores, so a component can be selected with
score at least the average while retaining a branchwise quantum footprint.
Selection does not preserve the mixture's channel or its operational error.
-/

namespace NLQCLean.ClassicalCommunication

attribute [local implicit_reducible] Matrix

/-- A normalized finite convex decomposition has a positive component count. -/
theorem mixedResource_component_count_pos {ρA ρB : Type*}
    [Fintype ρA] [Fintype ρB] {n : ℕ} (m : MixedResource ρA ρB n) : 0 < n := by
  by_cases hn : n = 0
  · subst n
    have h := m.weight_sum
    simp at h
  · exact Nat.pos_of_ne_zero hn

namespace FiniteClassicalProtocol

open Matrix

variable {ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype σA] [Fintype σB] [Fintype ηA] [Fintype ηB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable (P : FiniteClassicalProtocol
  ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB)

/-- Change the actual pure resource, leaving both instruments and all decoders fixed. -/
def withResource (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ) :
    FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
      σA σB ηA ηB ιA' ιB' εA εB :=
  { P with resource := γ, resource_unit := hγ }

/-- One actual pure component under the mixture's common local implementation. -/
def componentProtocol {n : ℕ} (m : MixedResource ρA ρB n) (k : Fin n) :=
  P.withResource (m.component k) (m.component_unit k)

@[simp] theorem componentProtocol_resource {n : ℕ}
    (m : MixedResource ρA ρB n) (k : Fin n) :
    (P.componentProtocol m k).resource = m.component k := rfl

/-- Common-map semantics: instruments and both outcome-dependent decoder
families are exactly the same in every component. -/
theorem componentProtocol_localMaps {n : ℕ} (m : MixedResource ρA ρB n) (k : Fin n) :
    (P.componentProtocol m k).instrumentA = P.instrumentA ∧
    (P.componentProtocol m k).instrumentB = P.instrumentB ∧
    (P.componentProtocol m k).decA = P.decA ∧
    (P.componentProtocol m k).decB = P.decB := ⟨rfl, rfl, rfl, rfl⟩

/-- The honest convex mixture of the actual component instrument channels. -/
def mixedOperationalChannel {n : ℕ} (m : MixedResource ρA ρB n) :
    Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ]
      Matrix (ιA' × ιB') (ιA' × ιB') ℂ :=
  ∑ k, (m.weight k : ℂ) • (P.componentProtocol m k).operationalChannel

/-- A one-component mixture is exactly its actual pure-component channel. -/
theorem mixedOperationalChannel_single (m : MixedResource ρA ρB 1) :
    P.mixedOperationalChannel m = (P.componentProtocol m 0).operationalChannel := by
  have hw : m.weight 0 = 1 := by simpa only [Fin.sum_univ_one] using m.weight_sum
  simp only [mixedOperationalChannel, Fin.sum_univ_one, hw, Complex.ofReal_one, one_smul]

section CoherentBridge

variable [DecidableEq σA] [DecidableEq σB] [DecidableEq ηA] [DecidableEq ηB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]

/-- Coherent copying and decoding use the same four local maps in every
resource component; only the resource vector changes. -/
theorem componentProtocol_coherentLocalMaps {n : ℕ}
    (m : MixedResource ρA ρB n) (k : Fin n) :
    (P.componentProtocol m k).coherentProtocol.encA = P.coherentProtocol.encA ∧
    (P.componentProtocol m k).coherentProtocol.encB = P.coherentProtocol.encB ∧
    (P.componentProtocol m k).coherentProtocol.decA = P.coherentProtocol.decA ∧
    (P.componentProtocol m k).coherentProtocol.decB = P.coherentProtocol.decB :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The actual finite mixed instrument channel is exactly an existing-model
common-map mixed channel under the genuine coherent conversion. This equality
holds before score-based component selection. -/
theorem mixedOperationalChannel_eq_coherentMixedChannel {n : ℕ}
    (m : MixedResource ρA ρB n) :
    P.mixedOperationalChannel m = m.mixedChannel
      P.coherentProtocol.encA P.coherentProtocol.encB
      P.coherentProtocol.decA P.coherentProtocol.decB := by
  rw [mixedOperationalChannel, MixedResource.mixedChannel]
  apply Finset.sum_congr rfl
  intro k _
  rw [← (P.componentProtocol m k).coherentProtocol_operationalChannel]
  rfl

end CoherentBridge

/-- One Schmidt-number cap applies to every component, and only the two
quantum message dimensions are charged. This is not a cap on mixed support. -/
def HasMixedQuantumFootprint {n : ℕ} (m : MixedResource ρA ρB n) (K : ℕ) : Prop :=
  ∃ R : ℕ, (∀ k, schmidtRank (P.componentProtocol m k).resource ≤ R) ∧
    R * Fintype.card μA * Fintype.card μB ≤ K

/-- The resource cap is exactly the original decomposition's Schmidt-number cap. -/
theorem hasMixedQuantumFootprint_iff_rank_bound {n : ℕ}
    (m : MixedResource ρA ρB n) (K : ℕ) :
    P.HasMixedQuantumFootprint m K ↔
      ∃ R : ℕ, m.schmidtNumberLE R ∧ R * Fintype.card μA * Fintype.card μB ≤ K := Iff.rfl

/-- The common mixed footprint is equivalent to a quantum footprint bound
on every actual component, including components of zero convex weight. -/
theorem hasMixedQuantumFootprint_iff_componentwise {n : ℕ}
    (m : MixedResource ρA ρB n) (K : ℕ) :
    P.HasMixedQuantumFootprint m K ↔
      ∀ k, (P.componentProtocol m k).HasQuantumFootprint K := by
  classical
  constructor
  · rintro ⟨R, hR, hK⟩ k
    apply (hasFootprint_iff K (P.componentProtocol m k).resource).mpr
    exact (Nat.mul_le_mul_right (Fintype.card μB)
      (Nat.mul_le_mul_right (Fintype.card μA) (hR k))).trans hK
  · intro hcomponents
    let : NeZero n := ⟨Nat.ne_of_gt (mixedResource_component_count_pos m)⟩
    obtain ⟨k₀, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
      (fun k => schmidtRank (P.componentProtocol m k).resource) Finset.univ_nonempty
    refine ⟨schmidtRank (P.componentProtocol m k₀).resource,
      (fun k => hmax k (Finset.mem_univ k)), ?_⟩
    exact (hasFootprint_iff K (P.componentProtocol m k₀).resource).mp (hcomponents k₀)

variable
  (S : (Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ]
    Matrix (ιA' × ιB') (ιA' × ιB') ℂ) →ₗ[ℝ] ℝ)

/-- Actual affinity of an arbitrary real-linear channel score in the finite mixture. -/
theorem linearScore_mixedOperationalChannel {n : ℕ} (m : MixedResource ρA ρB n) :
    S (P.mixedOperationalChannel m) =
      ∑ k, m.weight k * S (P.componentProtocol m k).operationalChannel := by
  rw [mixedOperationalChannel, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  change S (m.weight k • (P.componentProtocol m k).operationalChannel) = _
  simp only [map_smul, smul_eq_mul]

/-- Some actual pure component scores at least as highly as the mixture.
The finite decomposition is nonempty by its normalized convex weights. -/
theorem exists_component_linearScore_ge {n : ℕ} (m : MixedResource ρA ρB n) :
    ∃ k : Fin n, S (P.mixedOperationalChannel m) ≤
      S (P.componentProtocol m k).operationalChannel := by
  classical
  let : NeZero n := ⟨Nat.ne_of_gt (mixedResource_component_count_pos m)⟩
  obtain ⟨k₀, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun k => S (P.componentProtocol m k).operationalChannel) Finset.univ_nonempty
  refine ⟨k₀, ?_⟩
  rw [P.linearScore_mixedOperationalChannel S m]
  calc
    ∑ k, m.weight k * S (P.componentProtocol m k).operationalChannel ≤
        ∑ k, m.weight k * S (P.componentProtocol m k₀).operationalChannel :=
      Finset.sum_le_sum (fun k _ =>
        mul_le_mul_of_nonneg_left (hmax k (Finset.mem_univ k)) (m.weight_nonneg k))
    _ = S (P.componentProtocol m k₀).operationalChannel := by
      rw [← Finset.sum_mul, m.weight_sum, one_mul]

/-- Score nondecrease and the branchwise quantum footprint survive component
selection. No equality of channels or operational errors is asserted. -/
theorem exists_component_linearScore_ge_hasQuantumFootprint {n K : ℕ}
    (m : MixedResource ρA ρB n) (hK : P.HasMixedQuantumFootprint m K) :
    ∃ k : Fin n, S (P.mixedOperationalChannel m) ≤
      S (P.componentProtocol m k).operationalChannel ∧
      (P.componentProtocol m k).HasQuantumFootprint K := by
  obtain ⟨k, hscore⟩ := P.exists_component_linearScore_ge S m
  exact ⟨k, hscore, (P.hasMixedQuantumFootprint_iff_componentwise m K).mp hK k⟩

/-- An explicit Schmidt-number cap and message cost suffice for the selected
actual component to satisfy the pure protocol's quantum footprint bound. -/
theorem exists_component_linearScore_ge_of_rank_cost {n K R : ℕ}
    (m : MixedResource ρA ρB n) (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K) :
    ∃ k : Fin n, S (P.mixedOperationalChannel m) ≤
      S (P.componentProtocol m k).operationalChannel ∧
      (P.componentProtocol m k).HasQuantumFootprint K :=
  P.exists_component_linearScore_ge_hasQuantumFootprint S m
    ((P.hasMixedQuantumFootprint_iff_rank_bound m K).mpr ⟨R, hR, hK⟩)

end FiniteClassicalProtocol

end NLQCLean.ClassicalCommunication

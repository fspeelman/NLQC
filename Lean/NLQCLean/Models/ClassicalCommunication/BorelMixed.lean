import NLQCLean.Models.ClassicalCommunication.BorelRankCompression
import NLQCLean.Models.ClassicalCommunication.FiniteMixed

/-!
# Common-map finite mixed resources for standard-Borel instruments

Only the resource varies across the finite convex decomposition. Both actual
Borel instruments and all jointly measurable final local channels are shared.
The operational channel is the honest average of those actual component
channels. Schmidt number bounds every component rank and does not bound the
support of the mixed resource.
-/

namespace NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol

open Matrix
open scoped ComplexOrder

attribute [local implicit_reducible] Matrix

noncomputable section

variable {ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB' : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB']
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq ιA'] [DecidableEq ιB']
variable [MeasurableSpace σA] [MeasurableSpace σB]
variable [StandardBorelSpace σA] [StandardBorelSpace σB]
variable (P : StandardBorelClassicalProtocol
  ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB')

/-- Replace the resource while retaining both actual instruments and every
final channel, including its measurability and CP/TP proofs. -/
def withResource (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ) :
    StandardBorelClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA σB ιA' ιB' :=
  { P with resource := γ, resource_unit := hγ }

/-- An actual pure resource component under the same Borel local maps. -/
def componentProtocol {n : ℕ} (m : MixedResource ρA ρB n) (k : Fin n) :=
  P.withResource (m.component k) (m.component_unit k)

@[simp] theorem componentProtocol_resource {n : ℕ}
    (m : MixedResource ρA ρB n) (k : Fin n) :
    (P.componentProtocol m k).resource = m.component k := rfl

/-- The two instruments and both final channel families are common maps. -/
theorem componentProtocol_localMaps {n : ℕ} (m : MixedResource ρA ρB n) (k : Fin n) :
    (P.componentProtocol m k).instrumentA = P.instrumentA ∧
    (P.componentProtocol m k).instrumentB = P.instrumentB ∧
    (P.componentProtocol m k).decA = P.decA ∧
    (P.componentProtocol m k).decB = P.decB := ⟨rfl, rfl, rfl, rfl⟩

/-- The Schmidt-number cap charges only the two quantum message dimensions. -/
def HasMixedQuantumFootprint {n : ℕ} (m : MixedResource ρA ρB n) (K : ℕ) : Prop :=
  ∃ R : ℕ, (∀ k, schmidtRank (P.componentProtocol m k).resource ≤ R) ∧
    R * Fintype.card μA * Fintype.card μB ≤ K

/-- This is the original decomposition's rank cap, not a mixed support cap. -/
theorem hasMixedQuantumFootprint_iff_rank_bound {n : ℕ}
    (m : MixedResource ρA ρB n) (K : ℕ) :
    P.HasMixedQuantumFootprint m K ↔
      ∃ R : ℕ, m.schmidtNumberLE R ∧ R * Fintype.card μA * Fintype.card μB ≤ K := Iff.rfl

/-- Every actual component, including those of zero weight, satisfies the
same quantum footprint exactly when the common Schmidt-number cap does. -/
theorem hasMixedQuantumFootprint_iff_componentwise {n : ℕ}
    (m : MixedResource ρA ρB n) (K : ℕ) :
    P.HasMixedQuantumFootprint m K ↔
      ∀ k, (P.componentProtocol m k).HasQuantumFootprint K := by
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

variable [Nonempty ιA] [Nonempty ιB]

/-- Honest finite convex averaging of the original component channels,
before any score-based selection or coherent conversion. -/
def mixedOperationalChannel {n : ℕ} (m : MixedResource ρA ρB n) :
    Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ]
      Matrix (ιA' × ιB') (ιA' × ιB') ℂ :=
  ∑ k, (m.weight k : ℂ) • (P.componentProtocol m k).operationalChannel.toLinearMap

/-- A single-component mixed channel equals its actual component channel. -/
theorem mixedOperationalChannel_single (m : MixedResource ρA ρB 1) :
    P.mixedOperationalChannel m = (P.componentProtocol m 0).operationalChannel.toLinearMap := by
  have hw : m.weight 0 = 1 := by simpa only [Fin.sum_univ_one] using m.weight_sum
  simp only [mixedOperationalChannel, Fin.sum_univ_one, hw, Complex.ofReal_one, one_smul]

/-- Complete positivity of the actual common-map convex channel is derived
from the original Borel components. -/
theorem mixedOperationalChannel_completelyPositive {n : ℕ} (m : MixedResource ρA ρB n) :
    CompletelyPositive (P.mixedOperationalChannel m) := by
  apply (completelyPositive_iff_choiMatrix_posSemidef _).mpr
  have hchoi : choiMatrix (P.mixedOperationalChannel m) =
      ∑ k, (m.weight k : ℂ) • choiMatrix (P.componentProtocol m k).operationalChannel.toLinearMap := by
    ext p q
    simp only [mixedOperationalChannel, choiMatrix_sum_smul, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
  rw [hchoi]
  apply Matrix.posSemidef_sum
  intro k _
  exact (P.componentProtocol m k).operationalChannel_completelyPositive.choiMatrix_posSemidef.smul
    (Complex.nonneg_iff.mpr ⟨m.weight_nonneg k, rfl⟩)

/-- The honest average preserves every matrix trace. -/
theorem mixedOperationalChannel_tracePreserving {n : ℕ} (m : MixedResource ρA ρB n)
    (X : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    (P.mixedOperationalChannel m X).trace = X.trace := by
  have hTP (k : Fin n) :
      ((P.componentProtocol m k).operationalChannel.toLinearMap X).trace = X.trace :=
    (P.componentProtocol m k).operationalChannel_tracePreserving X
  simp only [mixedOperationalChannel, LinearMap.sum_apply, LinearMap.smul_apply,
    Matrix.trace_sum, Matrix.trace_smul, hTP, smul_eq_mul]
  rw [← Finset.sum_mul]
  have hw : ∑ k, (m.weight k : ℂ) = 1 := by exact_mod_cast m.weight_sum
  rw [hw, one_mul]

variable
  (S : (Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ]
    Matrix (ιA' × ιB') (ιA' × ιB') ℂ) →ₗ[ℝ] ℝ)

/-- Every real-linear channel score has its actual convex-average value. -/
theorem linearScore_mixedOperationalChannel {n : ℕ} (m : MixedResource ρA ρB n) :
    S (P.mixedOperationalChannel m) =
      ∑ k, m.weight k * S (P.componentProtocol m k).operationalChannel.toLinearMap := by
  rw [mixedOperationalChannel, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  change S (m.weight k • (P.componentProtocol m k).operationalChannel.toLinearMap) = _
  simp only [map_smul, smul_eq_mul]

/-- An actual pure component scores at least the honest mixed channel. -/
theorem exists_component_linearScore_ge {n : ℕ} (m : MixedResource ρA ρB n) :
    ∃ k : Fin n, S (P.mixedOperationalChannel m) ≤
      S (P.componentProtocol m k).operationalChannel.toLinearMap := by
  let : NeZero n := ⟨Nat.ne_of_gt (mixedResource_component_count_pos m)⟩
  obtain ⟨k₀, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun k => S (P.componentProtocol m k).operationalChannel.toLinearMap) Finset.univ_nonempty
  refine ⟨k₀, ?_⟩
  rw [P.linearScore_mixedOperationalChannel S m]
  calc
    ∑ k, m.weight k * S (P.componentProtocol m k).operationalChannel.toLinearMap ≤
        ∑ k, m.weight k * S (P.componentProtocol m k₀).operationalChannel.toLinearMap :=
      Finset.sum_le_sum (fun k _ =>
        mul_le_mul_of_nonneg_left (hmax k (Finset.mem_univ k)) (m.weight_nonneg k))
    _ = S (P.componentProtocol m k₀).operationalChannel.toLinearMap := by
      rw [← Finset.sum_mul, m.weight_sum, one_mul]

/-- Component selection retains both score nondecrease and the quantum cap. -/
theorem exists_component_linearScore_ge_hasQuantumFootprint {n K : ℕ}
    (m : MixedResource ρA ρB n) (hK : P.HasMixedQuantumFootprint m K) :
    ∃ k : Fin n, S (P.mixedOperationalChannel m) ≤
      S (P.componentProtocol m k).operationalChannel.toLinearMap ∧
      (P.componentProtocol m k).HasQuantumFootprint K := by
  obtain ⟨k, hscore⟩ := P.exists_component_linearScore_ge S m
  exact ⟨k, hscore, (P.hasMixedQuantumFootprint_iff_componentwise m K).mp hK k⟩

/-- A Schmidt-number cap and the cost of both quantum messages suffice. -/
theorem exists_component_linearScore_ge_of_rank_cost {n K R : ℕ}
    (m : MixedResource ρA ρB n) (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K) :
    ∃ k : Fin n, S (P.mixedOperationalChannel m) ≤
      S (P.componentProtocol m k).operationalChannel.toLinearMap ∧
      (P.componentProtocol m k).HasQuantumFootprint K :=
  P.exists_component_linearScore_ge_hasQuantumFootprint S m
    ((P.hasMixedQuantumFootprint_iff_rank_bound m K).mpr ⟨R, hR, hK⟩)

end

end NLQCLean.ClassicalCommunication.StandardBorelClassicalProtocol

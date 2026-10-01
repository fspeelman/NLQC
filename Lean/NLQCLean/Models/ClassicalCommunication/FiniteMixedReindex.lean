import NLQCLean.Models.ClassicalCommunication.FiniteProtocolReindex
import NLQCLean.Models.ClassicalCommunication.FiniteMixed

/-! # Relabeling common-map finite mixed protocols

The finite ensemble is transported together with the common instruments and
decoders. Each component's Schmidt rank, the original averaged channel and
both quantum message charges are preserved.
-/

namespace NLQCLean.MixedResource

noncomputable section

variable {ρA ρB ρA₂ ρB₂ : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype ρA₂] [Fintype ρB₂]

/-- Transport every pure component, retaining the original convex weights. -/
def reindexRegisters {n : ℕ} (m : MixedResource ρA ρB n)
    (rA : ρA₂ ≃ ρA) (rB : ρB₂ ≃ ρB) : MixedResource ρA₂ ρB₂ n where
  weight := m.weight
  weight_nonneg := m.weight_nonneg
  weight_sum := m.weight_sum
  component k := m.component k ∘ rA.prodCongr rB
  component_unit k := (m.component_unit k).comp_equiv (rA.prodCongr rB)

@[simp] theorem schmidtRank_component_reindexRegisters {n : ℕ}
    (m : MixedResource ρA ρB n) (rA : ρA₂ ≃ ρA) (rB : ρB₂ ≃ ρB) (k : Fin n) :
    schmidtRank ((m.reindexRegisters rA rB).component k) = schmidtRank (m.component k) :=
  Matrix.rank_submatrix (resourceMatrix (m.component k)) rA rB

/-- The decomposition's Schmidt-number cap is unchanged, including zero weights. -/
theorem schmidtNumberLE_reindexRegisters {n R : ℕ} (m : MixedResource ρA ρB n)
    (rA : ρA₂ ≃ ρA) (rB : ρB₂ ≃ ρB) :
    (m.reindexRegisters rA rB).schmidtNumberLE R ↔ m.schmidtNumberLE R := by
  simp only [schmidtNumberLE, schmidtRank_component_reindexRegisters]

end
end NLQCLean.MixedResource

namespace NLQCLean.ClassicalCommunication.FiniteClassicalProtocol

open Matrix
attribute [local implicit_reducible] Matrix
noncomputable section

variable {ιA ιB ιA' ιB' ρA ρB κA κB μA μB σA σB ηA ηB εA εB
    ρA₂ ρB₂ κA₂ κB₂ μA₂ μB₂ σA₂ σB₂ ηA₂ ηB₂ εA₂ εB₂ : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ιA'] [Fintype ιB']
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
variable [Fintype ηA] [Fintype ηB] [Fintype εA] [Fintype εB]
variable [Fintype ρA₂] [Fintype ρB₂] [Fintype κA₂] [Fintype κB₂]
variable [Fintype μA₂] [Fintype μB₂] [Fintype σA₂] [Fintype σB₂]
variable [Fintype ηA₂] [Fintype ηB₂] [Fintype εA₂] [Fintype εB₂]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ιA'] [DecidableEq ιB']
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq σA] [DecidableEq σB]
variable [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB]
variable [DecidableEq ρA₂] [DecidableEq ρB₂] [DecidableEq κA₂] [DecidableEq κB₂]
variable [DecidableEq μA₂] [DecidableEq μB₂] [DecidableEq σA₂] [DecidableEq σB₂]
variable [DecidableEq ηA₂] [DecidableEq ηB₂] [DecidableEq εA₂] [DecidableEq εB₂]

variable (P : FiniteClassicalProtocol
  ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB)
variable (rA : ρA₂ ≃ ρA) (rB : ρB₂ ≃ ρB) (kA : κA₂ ≃ κA) (kB : κB₂ ≃ κB)
variable (mA : μA₂ ≃ μA) (mB : μB₂ ≃ μB) (sA : σA₂ ≃ σA) (sB : σB₂ ≃ σB)
variable (hA : ηA₂ ≃ ηA) (hB : ηB₂ ≃ ηB) (eA : εA₂ ≃ εA) (eB : εB₂ ≃ εB)

omit [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq σA] [DecidableEq σB]
  [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB]
  [DecidableEq σA₂] [DecidableEq σB₂] [DecidableEq ηA₂] [DecidableEq ηB₂]
  [DecidableEq εA₂] [DecidableEq εB₂] in
/-- Relabeling commutes with choosing a component under the common local maps. -/
theorem componentProtocol_reindex {n : ℕ} (m : MixedResource ρA ρB n) (k : Fin n) :
    (P.reindex rA rB kA kB mA mB sA sB hA hB eA eB).componentProtocol
      (m.reindexRegisters rA rB) k =
    (P.componentProtocol m k).reindex rA rB kA kB mA mB sA sB hA hB eA eB := rfl

omit [DecidableEq σA] [DecidableEq σB] [DecidableEq ηA] [DecidableEq ηB]
  [DecidableEq σA₂] [DecidableEq σB₂] [DecidableEq ηA₂] [DecidableEq ηB₂] in
/-- Basis transport preserves the original common-map averaged operational channel. -/
theorem mixedOperationalChannel_reindex {n : ℕ} (m : MixedResource ρA ρB n) :
    (P.reindex rA rB kA kB mA mB sA sB hA hB eA eB).mixedOperationalChannel
      (m.reindexRegisters rA rB) = P.mixedOperationalChannel m := by
  unfold mixedOperationalChannel
  apply Finset.sum_congr rfl
  intro k _
  change (m.weight k : ℂ) •
    ((P.componentProtocol m k).reindex rA rB kA kB mA mB sA sB hA hB eA eB).operationalChannel =
      (m.weight k : ℂ) • (P.componentProtocol m k).operationalChannel
  exact congrArg (fun C => (m.weight k : ℂ) • C)
    ((P.componentProtocol m k).operationalChannel_reindex rA rB kA kB mA mB sA sB hA hB eA eB)

omit [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq σA] [DecidableEq σB]
  [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB]
  [DecidableEq σA₂] [DecidableEq σB₂] [DecidableEq ηA₂] [DecidableEq ηB₂]
  [DecidableEq εA₂] [DecidableEq εB₂] in
/-- Each component and the common message cap retain their original quantum charge. -/
theorem mixedQuantumFootprint_reindex {n : ℕ} (m : MixedResource ρA ρB n) (K : ℕ) :
    (P.reindex rA rB kA kB mA mB sA sB hA hB eA eB).HasMixedQuantumFootprint
      (m.reindexRegisters rA rB) K ↔ P.HasMixedQuantumFootprint m K := by
  simp only [hasMixedQuantumFootprint_iff_rank_bound,
    MixedResource.schmidtNumberLE_reindexRegisters, Fintype.card_congr mA,
    Fintype.card_congr mB]

omit [DecidableEq σA] [DecidableEq σB] [DecidableEq ηA] [DecidableEq ηB] in
theorem mixedOperationalChannel_toFin {n : ℕ} (m : MixedResource ρA ρB n) :
    P.toFin.mixedOperationalChannel
      (m.reindexRegisters (Fintype.equivFin ρA).symm (Fintype.equivFin ρB).symm) =
      P.mixedOperationalChannel m :=
  P.mixedOperationalChannel_reindex _ _ _ _ _ _ _ _ _ _ _ _ m

omit [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq σA] [DecidableEq σB]
  [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB] in
theorem mixedQuantumFootprint_toFin {n : ℕ} (m : MixedResource ρA ρB n) (K : ℕ) :
    P.toFin.HasMixedQuantumFootprint
      (m.reindexRegisters (Fintype.equivFin ρA).symm (Fintype.equivFin ρB).symm) K ↔
      P.HasMixedQuantumFootprint m K :=
  P.mixedQuantumFootprint_reindex _ _ _ _ _ _ _ _ _ _ _ _ m K

end
end NLQCLean.ClassicalCommunication.FiniteClassicalProtocol

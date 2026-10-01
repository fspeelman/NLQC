import NLQCLean.Models.ClassicalCommunication.FiniteProtocol
import NLQCLean.Models.ClassicalCommunication.FiniteInstrumentReindex

/-! # Relabeling the internal registers of finite classical protocols

Outcome and private Kraus labels, resource bases, workspaces and both quantum
messages may be transported independently. Logical inputs and outputs stay
fixed. The actual operational channel and quantum footprint are preserved.
-/

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

/-- An actual finite instrument protocol with all internal labels transported. -/
def reindex : FiniteClassicalProtocol
    ιA ιB ρA₂ ρB₂ κA₂ κB₂ μA₂ μB₂ σA₂ σB₂ ηA₂ ηB₂ ιA' ιB' εA₂ εB₂ where
  resource := P.resource ∘ rA.prodCongr rB
  resource_unit := P.resource_unit.comp_equiv (rA.prodCongr rB)
  instrumentA := P.instrumentA.reindex ((Equiv.refl ιA).prodCongr rA)
    (kA.prodCongr mA) sA hA
  instrumentB := P.instrumentB.reindex ((Equiv.refl ιB).prodCongr rB)
    (kB.prodCongr mB) sB hB
  decA x y := (P.decA (sA x) (sB y)).submatrix
    ((Equiv.refl ιA').prodCongr eA) (kA.prodCongr mB)
  decB x y := (P.decB (sA x) (sB y)).submatrix
    ((Equiv.refl ιB').prodCongr eB) (kB.prodCongr mA)
  decA_isometry x y := (P.decA_isometry (sA x) (sB y)).submatrix_equiv _ _
  decB_isometry x y := (P.decB_isometry (sA x) (sB y)).submatrix_equiv _ _

omit [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq σA] [DecidableEq σB]
  [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB]
  [DecidableEq σA₂] [DecidableEq σB₂] [DecidableEq ηA₂] [DecidableEq ηB₂]
  [DecidableEq εA₂] [DecidableEq εB₂] in
/-- Individual unnormalized branch amplitudes retain the same physical entries. -/
theorem branchAmplitude_reindex (x : σA₂) (y : σB₂) (a : ηA₂) (b : ηB₂) :
    (P.reindex rA rB kA kB mA mB sA sB hA hB eA eB).branchAmplitude x y a b =
      (P.branchAmplitude (sA x) (sB y) (hA a) (hB b)).submatrix
        (((Equiv.refl ιA').prodCongr eA).prodCongr
          ((Equiv.refl ιB').prodCongr eB)) id :=
  globalIsometry_reindex rA rB kA kB mA mB eA eB P.resource
    (P.instrumentA.operator (sA x) (hA a))
    (P.instrumentB.operator (sB y) (hB b)) (P.decA (sA x) (sB y))
    (P.decB (sA x) (sB y))

omit [DecidableEq σA] [DecidableEq σB] [DecidableEq ηA] [DecidableEq ηB]
  [DecidableEq σA₂] [DecidableEq σB₂] [DecidableEq ηA₂] [DecidableEq ηB₂] in
private theorem branchChannel_reindex (x : σA₂) (y : σB₂) (a : ηA₂) (b : ηB₂) :
    channelOf (((P.reindex rA rB kA kB mA mB sA sB hA hB eA eB).branchAmplitude
      x y a b).submatrix (outputRegroup ιA' ιB' εA₂ εB₂) id) =
    channelOf ((P.branchAmplitude (sA x) (sB y) (hA a) (hB b)).submatrix
      (outputRegroup ιA' ιB' εA εB) id) := by
  rw [branchAmplitude_reindex]
  have hreg (F : Matrix ((ιA' × εA) × (ιB' × εB)) (ιA × ιB) ℂ) :
      (F.submatrix (((Equiv.refl ιA').prodCongr eA).prodCongr
        ((Equiv.refl ιB').prodCongr eB)) id).submatrix
          (outputRegroup ιA' ιB' εA₂ εB₂) id =
      (F.submatrix (outputRegroup ιA' ιB' εA εB) id).submatrix
        ((Equiv.refl (ιA' × ιB')).prodCongr (eA.prodCongr eB)) id := by
    ext p q
    rfl
  rw [hreg]
  exact channelOf_reindex_environment (eA.prodCongr eB) _

omit [DecidableEq σA] [DecidableEq σB] [DecidableEq ηA] [DecidableEq ηB]
  [DecidableEq σA₂] [DecidableEq σB₂] [DecidableEq ηA₂] [DecidableEq ηB₂] in
/-- Summing the relabeled branches leaves the original operational channel unchanged. -/
theorem operationalChannel_reindex :
    (P.reindex rA rB kA kB mA mB sA sB hA hB eA eB).operationalChannel =
      P.operationalChannel := by
  simp only [operationalChannel]
  simp_rw [branchChannel_reindex]
  simpa only [Fintype.sum_prod_type, Equiv.prodCongr_apply, Prod.map] using
    (sA.prodCongr (sB.prodCongr (hA.prodCongr hB))).sum_comp
      (fun p : σA × (σB × (ηA × ηB)) =>
        channelOf ((P.branchAmplitude p.1 p.2.1 p.2.2.1 p.2.2.2).submatrix
          (outputRegroup ιA' ιB' εA εB) id))

omit [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq σA] [DecidableEq σB]
  [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB]
  [DecidableEq σA₂] [DecidableEq σB₂] [DecidableEq ηA₂] [DecidableEq ηB₂]
  [DecidableEq εA₂] [DecidableEq εB₂] in
/-- Relabeling resource and message bases preserves the rank-based quantum charge. -/
theorem quantumFootprint_reindex (K : ℕ) :
    (P.reindex rA rB kA kB mA mB sA sB hA hB eA eB).HasQuantumFootprint K ↔
      P.HasQuantumFootprint K := by
  have hrank : schmidtRank (P.resource ∘ rA.prodCongr rB) = schmidtRank P.resource :=
    Matrix.rank_submatrix (resourceMatrix P.resource) rA rB
  change HasFootprint K (P.resource ∘ rA.prodCongr rB) μA₂ μB₂ ↔
    HasFootprint K P.resource μA μB
  simp only [hasFootprint_iff]
  rw [hrank, Fintype.card_congr mA, Fintype.card_congr mB]

/-- Canonical finite labels for every internal register, retaining the actual maps. -/
def toFin : FiniteClassicalProtocol ιA ιB
    (Fin (Fintype.card ρA)) (Fin (Fintype.card ρB))
    (Fin (Fintype.card κA)) (Fin (Fintype.card κB))
    (Fin (Fintype.card μA)) (Fin (Fintype.card μB))
    (Fin (Fintype.card σA)) (Fin (Fintype.card σB))
    (Fin (Fintype.card ηA)) (Fin (Fintype.card ηB)) ιA' ιB'
    (Fin (Fintype.card εA)) (Fin (Fintype.card εB)) :=
  P.reindex (Fintype.equivFin ρA).symm (Fintype.equivFin ρB).symm
    (Fintype.equivFin κA).symm (Fintype.equivFin κB).symm
    (Fintype.equivFin μA).symm (Fintype.equivFin μB).symm
    (Fintype.equivFin σA).symm (Fintype.equivFin σB).symm
    (Fintype.equivFin ηA).symm (Fintype.equivFin ηB).symm
    (Fintype.equivFin εA).symm (Fintype.equivFin εB).symm

omit [DecidableEq σA] [DecidableEq σB] [DecidableEq ηA] [DecidableEq ηB] in
theorem operationalChannel_toFin : P.toFin.operationalChannel = P.operationalChannel :=
  P.operationalChannel_reindex _ _ _ _ _ _ _ _ _ _ _ _

omit [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq σA] [DecidableEq σB]
  [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB] in
theorem quantumFootprint_toFin (K : ℕ) :
    P.toFin.HasQuantumFootprint K ↔ P.HasQuantumFootprint K :=
  P.quantumFootprint_reindex _ _ _ _ _ _ _ _ _ _ _ _ K

end

end NLQCLean.ClassicalCommunication.FiniteClassicalProtocol

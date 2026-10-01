import NLQCLean.Models.ClassicalCommunication.CoherentLabels
import NLQCLean.Models.ClassicalCommunication.FiniteSupport
import NLQCLean.Models.Resource

/-!
# Finite simultaneous classical communication

Each party applies an actual finite Kraus instrument and sends a fixed
quantum message together with its classical outcome. Final local channels
may depend on both outcomes. The quantum footprint charges only the resource
Schmidt rank and quantum messages. The coherent conversion separately charges
the copied outcome alphabets, retaining all private Kraus labels locally.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix
open scoped Kronecker

/-- Operational finite-outcome data. Final channels are given by their actual
finite Stinespring isometries, not by an assumed coherent representation. -/
structure FiniteClassicalProtocol
    (ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB : Type*)
    [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
    [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
    [Fintype σA] [Fintype σB] [Fintype ηA] [Fintype ηB]
    [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
    [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
    [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB] where
  resource : ρA × ρB → ℂ
  resource_unit : IsUnitVector resource
  instrumentA : FiniteKrausInstrument (ιA × ρA) (κA × μA) σA ηA
  instrumentB : FiniteKrausInstrument (ιB × ρB) (κB × μB) σB ηB
  decA : σA → σB → Matrix (ιA' × εA) (κA × μB) ℂ
  decB : σA → σB → Matrix (ιB' × εB) (κB × μA) ℂ
  decA_isometry : ∀ x y, IsIsometry (decA x y)
  decB_isometry : ∀ x y, IsIsometry (decB x y)

namespace FiniteClassicalProtocol

variable {ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype σA] [Fintype σB] [Fintype ηA] [Fintype ηB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq σA] [DecidableEq σB] [DecidableEq ηA] [DecidableEq ηB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]
variable (P : FiniteClassicalProtocol
  ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB)

/-- The quantum-only footprint leaves the classical alphabets uncharged. -/
def HasQuantumFootprint (K : ℕ) : Prop := HasFootprint K P.resource μA μB

/-- The unnormalized physical amplitude of one pair of outcomes and Kraus
labels. This uses the same canonical message exchange as the existing model. -/
def branchAmplitude (x : σA) (y : σB) (e : ηA) (f : ηB) :
    Matrix ((ιA' × εA) × (ιB' × εB)) (ιA × ιB) ℂ :=
  NLQCLean.globalIsometry P.resource (P.instrumentA.operator x e)
    (P.instrumentB.operator y f) (P.decA x y) (P.decB x y)

/-- Actual instrument probabilities are included in the Kraus amplitudes;
branches are summed without an artificial normalization of each outcome. -/
def operationalChannel :
    Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ] Matrix (ιA' × ιB') (ιA' × ιB') ℂ :=
  ∑ x, ∑ y, ∑ e, ∑ f,
    channelOf ((P.branchAmplitude x y e f).submatrix
      (outputRegroup ιA' ιB' εA εB) id)

/-- Ordinary coherent protocols are the one-outcome, one-Kraus specialization. -/
def ofPureProtocol (Q : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB) :
    FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB Unit Unit Unit Unit
      ιA' ιB' εA εB where
  resource := Q.resource
  resource_unit := Q.resource_unit
  instrumentA := FiniteKrausInstrument.ofIsometry Q.encA Q.encA_isometry
  instrumentB := FiniteKrausInstrument.ofIsometry Q.encB Q.encB_isometry
  decA := fun _ _ => Q.decA
  decB := fun _ _ => Q.decB
  decA_isometry := fun _ _ => Q.decA_isometry
  decB_isometry := fun _ _ => Q.decB_isometry

/-- The specialization has exactly the original operational channel. -/
theorem operationalChannel_ofPureProtocol
    (Q : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB) :
    (ofPureProtocol Q).operationalChannel = Q.operationalChannel := by
  simp only [operationalChannel, Fintype.sum_unique]
  rfl

/-- Its quantum footprint is exactly the original charged-message footprint. -/
theorem quantumFootprint_ofPureProtocol
    (Q : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB) (K : ℕ) :
    (ofPureProtocol Q).HasQuantumFootprint K ↔ Q.HasFootprint K := Iff.rfl

private def decoderRowEquiv (o v label : Type*) :
    o × (v × label) ≃ (o × v) × label := (Equiv.prodAssoc o v label).symm

private def decoderAColEquiv :
    (κA × (σA × ηA)) × (μB × σB) ≃ (κA × μB) × (σA × (σB × ηA)) where
  toFun p := ((p.1.1, p.2.1), (p.1.2.1, (p.2.2, p.1.2.2)))
  invFun p := ((p.1.1, (p.2.1, p.2.2.2)), (p.1.2, p.2.2.1))
  left_inv := by rintro ⟨⟨_, ⟨_, _⟩⟩, ⟨_, _⟩⟩; rfl
  right_inv := by rintro ⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩; rfl

private def decoderBColEquiv :
    (κB × (σB × ηB)) × (μA × σA) ≃ (κB × μA) × (σA × (σB × ηB)) where
  toFun p := ((p.1.1, p.2.1), (p.2.2, (p.1.2.1, p.1.2.2)))
  invFun p := ((p.1.1, (p.2.2.1, p.2.2.2)), (p.1.2, p.2.1))
  left_inv := by rintro ⟨⟨_, ⟨_, _⟩⟩, ⟨_, _⟩⟩; rfl
  right_inv := by rintro ⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩; rfl

/-- Alice retains both outcomes and her private Kraus label in the final
environment, and acts with the prescribed final channel in each sector. -/
def coherentDecoderA :
    Matrix (ιA' × (εA × (σA × (σB × ηA))))
      ((κA × (σA × ηA)) × (μB × σB)) ℂ :=
  Matrix.of fun p q => if p.2.2 = (q.1.2.1, (q.2.2, q.1.2.2)) then
    P.decA q.1.2.1 q.2.2 (p.1, p.2.1) (q.1.1, q.2.1) else 0

/-- Bob also retains both outcomes; his Kraus label remains private. -/
def coherentDecoderB :
    Matrix (ιB' × (εB × (σA × (σB × ηB))))
      ((κB × (σB × ηB)) × (μA × σA)) ℂ :=
  Matrix.of fun p q => if p.2.2 = (q.2.2, (q.1.2.1, q.1.2.2)) then
    P.decB q.2.2 q.1.2.1 (p.1, p.2.1) (q.1.1, q.2.1) else 0

omit [DecidableEq ηB] [DecidableEq ιA'] [DecidableEq ιB']
  [DecidableEq εA] [DecidableEq εB] in
@[simp] theorem coherentDecoderA_apply
    (p : ιA' × (εA × (σA × (σB × ηA))))
    (q : (κA × (σA × ηA)) × (μB × σB)) :
    P.coherentDecoderA p q =
      if p.2.2 = (q.1.2.1, (q.2.2, q.1.2.2)) then
        P.decA q.1.2.1 q.2.2 (p.1, p.2.1) (q.1.1, q.2.1) else 0 := rfl

omit [DecidableEq ηA] [DecidableEq ιA'] [DecidableEq ιB']
  [DecidableEq εA] [DecidableEq εB] in
@[simp] theorem coherentDecoderB_apply
    (p : ιB' × (εB × (σA × (σB × ηB))))
    (q : (κB × (σB × ηB)) × (μA × σA)) :
    P.coherentDecoderB p q =
      if p.2.2 = (q.2.2, (q.1.2.1, q.1.2.2)) then
        P.decB q.2.2 q.1.2.1 (p.1, p.2.1) (q.1.1, q.2.1) else 0 := rfl

omit [DecidableEq ηB] [DecidableEq ιA'] [DecidableEq ιB']
  [DecidableEq εA] [DecidableEq εB] in
theorem coherentDecoderA_isometry : IsIsometry P.coherentDecoderA := by
  change IsIsometry
    ((controlledMatrix (fun l : σA × (σB × ηA) => P.decA l.1 l.2.1)).submatrix
      (decoderRowEquiv _ _ _) decoderAColEquiv)
  exact (controlledMatrix_isometry _ (fun _ => P.decA_isometry _ _)).submatrix_equiv _ _

omit [DecidableEq ηA] [DecidableEq ιA'] [DecidableEq ιB']
  [DecidableEq εA] [DecidableEq εB] in
theorem coherentDecoderB_isometry : IsIsometry P.coherentDecoderB := by
  change IsIsometry
    ((controlledMatrix (fun l : σA × (σB × ηB) => P.decB l.1 l.2.1)).submatrix
      (decoderRowEquiv _ _ _) decoderBColEquiv)
  exact (controlledMatrix_isometry _ (fun _ => P.decB_isometry _ _)).submatrix_equiv _ _

/-- A genuine protocol in the existing charged-message model. The outcome
alphabets enter the messages; Kraus indices enter only the private workspaces. -/
def coherentProtocol : PureProtocol ιA ιB ρA ρB
    (κA × (σA × ηA)) (κB × (σB × ηB)) (μA × σA) (μB × σB)
    ιA' ιB' (εA × (σA × (σB × ηA))) (εB × (σA × (σB × ηB))) where
  resource := P.resource
  resource_unit := P.resource_unit
  encA := P.instrumentA.coherentEncoder
  encB := P.instrumentB.coherentEncoder
  encA_isometry := P.instrumentA.coherentEncoder_isometry
  encB_isometry := P.instrumentB.coherentEncoder_isometry
  decA := P.coherentDecoderA
  decB := P.coherentDecoderB
  decA_isometry := P.coherentDecoderA_isometry
  decB_isometry := P.coherentDecoderB_isometry

/-- Exact charged footprint of the explicit coherent architecture. -/
theorem coherentProtocol_hasFootprint_iff (K : ℕ) :
    P.coherentProtocol.HasFootprint K ↔
      schmidtRank P.resource * (Fintype.card μA * Fintype.card σA) *
        (Fintype.card μB * Fintype.card σB) ≤ K := by
  simp only [PureProtocol.HasFootprint, hasFootprint_iff, coherentProtocol,
    Fintype.card_prod]

/-- With already bounded outcome alphabets, the actual physical conversion
has the fifth-power charged footprint. This does not assume alphabet compression. -/
theorem coherentProtocol_hasFootprint (d K : ℕ)
    (hmA : 1 ≤ Fintype.card μA) (hmB : 1 ≤ Fintype.card μB)
    (hK : P.HasQuantumFootprint K)
    (haA : Fintype.card σA ≤ 2 * d ^ 2 * (schmidtRank P.resource) ^ 2)
    (haB : Fintype.card σB ≤ 2 * d ^ 2 * (schmidtRank P.resource) ^ 2) :
    P.coherentProtocol.HasFootprint (4 * d ^ 4 * K ^ 5) := by
  rw [coherentProtocol_hasFootprint_iff]
  apply charged_message_footprint_le d _ _ _ _ _ K hmA hmB
  · exact (hasFootprint_iff _ _).mp hK
  · exact haA
  · exact haB

end FiniteClassicalProtocol

end NLQCLean.ClassicalCommunication

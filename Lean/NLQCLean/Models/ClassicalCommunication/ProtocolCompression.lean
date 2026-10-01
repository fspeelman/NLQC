import NLQCLean.Models.ClassicalCommunication.BranchChannels
import NLQCLean.Models.ClassicalCommunication.InstrumentCompression
import NLQCLean.LinearAlgebra.SupportFactorization

/-!
# Score-preserving finite classical outcome compression

Compress Alice's actual instrument while Bob and both outcome-dependent
decoders are fixed, then compress Bob with the selected Alice instrument
fixed. Every selected operation is realized by its square-root-rescaled
original Kraus matrices. Only the outcome alphabets change: the resource,
quantum messages, private Kraus systems, and final environments are retained.
-/

namespace NLQCLean.ClassicalCommunication.FiniteClassicalProtocol

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

/-- Replace Alice's instrument and use the original decoders at selected outcomes. -/
def replaceAliceInstrument {τ : Type*} [Fintype τ]
    (J : FiniteKrausInstrument (ιA × ρA) (κA × μA) τ ηA)
    (select : τ → σA) :
    FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB τ σB ηA ηB ιA' ιB' εA εB where
  resource := P.resource
  resource_unit := P.resource_unit
  instrumentA := J
  instrumentB := P.instrumentB
  decA := fun j y => P.decA (select j) y
  decB := fun j y => P.decB (select j) y
  decA_isometry := fun j y => P.decA_isometry (select j) y
  decB_isometry := fun j y => P.decB_isometry (select j) y

/-- Replace Bob's instrument, retaining Alice and the original decoder choices. -/
def replaceBobInstrument {τ : Type*} [Fintype τ]
    (J : FiniteKrausInstrument (ιB × ρB) (κB × μB) τ ηB)
    (select : τ → σB) :
    FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB σA τ ηA ηB ιA' ιB' εA εB where
  resource := P.resource
  resource_unit := P.resource_unit
  instrumentA := P.instrumentA
  instrumentB := J
  decA := fun x j => P.decA x (select j)
  decB := fun x j => P.decB x (select j)
  decA_isometry := fun x j => P.decA_isometry x (select j)
  decB_isometry := fun x j => P.decB_isometry x (select j)

variable
  (S : (Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ]
    Matrix (ιA' × ιB') (ιA' × ιB') ℂ) →ₗ[ℝ] ℝ)

/-- Alice's selected actual outcomes preserve a prescribed real-linear score,
including all of Bob's fixed outcomes and the actual final channels. -/
theorem exists_compressAlice_preserving_linearScore [Nonempty ιA] :
    ∃ n : ℕ, n ≤ Fintype.card (ιA × ρA) ^ 2 + 1 ∧
      ∃ (select : Fin n → σA) (scale : Fin n → ℝ)
        (Q : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
          (Fin n) σB ηA ηB ιA' ιB' εA εB),
        (∀ j, 0 ≤ scale j) ∧ Q.resource = P.resource ∧
        Q.instrumentB = P.instrumentB ∧
        (∀ j e, Q.instrumentA.operator j e =
          (Real.sqrt (scale j) : ℂ) • P.instrumentA.operator (select j) e) ∧
        (∀ j y, Q.decA j y = P.decA (select j) y) ∧
        (∀ j y, Q.decB j y = P.decB (select j) y) ∧
        S Q.operationalChannel = S P.operationalChannel := by
  classical
  have hρ := Fintype.card_pos_iff.mp P.resource_unit.card_pos
  let : Nonempty ρA := hρ.map Prod.fst
  let L : σA → ((Matrix (ιA × ρA) (ιA × ρA) ℂ →ₗ[ℂ]
      Matrix (κA × μA) (κA × μA) ℂ) →ₗ[ℝ] ℝ) := fun x =>
    ∑ y, S.comp (branchChannelLeftRealLinear P.resource (P.decA x y)
      (P.decB x y) (P.instrumentB.branch y))
  obtain ⟨n, hn, select, scale, J, hscale, hops, _, hsum⟩ :=
    P.instrumentA.exists_score_preserving_compression L
  let Q := P.replaceAliceInstrument J select
  refine ⟨n, hn, select, scale, Q, hscale, rfl, rfl, hops,
    (fun _ _ => rfl), (fun _ _ => rfl), ?_⟩
  calc
    S Q.operationalChannel = ∑ j, L (select j) (J.branch j) := by
      rw [Q.operationalChannel_eq_sum_outcomeChannel]
      simp only [map_sum, L, LinearMap.sum_apply, LinearMap.comp_apply,
        branchChannelLeftRealLinear_apply, Q, replaceAliceInstrument, outcomeChannel]
    _ = ∑ x, L x (P.instrumentA.branch x) := hsum
    _ = S P.operationalChannel := by
      rw [P.operationalChannel_eq_sum_outcomeChannel]
      simp only [map_sum, L, LinearMap.sum_apply, LinearMap.comp_apply,
        branchChannelLeftRealLinear_apply, outcomeChannel]

/-- Bob is compressed after fixing Alice's actual instrument. The scalar
moment includes every fixed Alice outcome before actual Bob outcomes are selected. -/
theorem exists_compressBob_preserving_linearScore [Nonempty ιB] :
    ∃ n : ℕ, n ≤ Fintype.card (ιB × ρB) ^ 2 + 1 ∧
      ∃ (select : Fin n → σB) (scale : Fin n → ℝ)
        (Q : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
          σA (Fin n) ηA ηB ιA' ιB' εA εB),
        (∀ j, 0 ≤ scale j) ∧ Q.resource = P.resource ∧
        Q.instrumentA = P.instrumentA ∧
        (∀ j e, Q.instrumentB.operator j e =
          (Real.sqrt (scale j) : ℂ) • P.instrumentB.operator (select j) e) ∧
        (∀ x j, Q.decA x j = P.decA x (select j)) ∧
        (∀ x j, Q.decB x j = P.decB x (select j)) ∧
        S Q.operationalChannel = S P.operationalChannel := by
  classical
  have hρ := Fintype.card_pos_iff.mp P.resource_unit.card_pos
  let : Nonempty ρB := hρ.map Prod.snd
  let L : σB → ((Matrix (ιB × ρB) (ιB × ρB) ℂ →ₗ[ℂ]
      Matrix (κB × μB) (κB × μB) ℂ) →ₗ[ℝ] ℝ) := fun y =>
    ∑ x, S.comp (branchChannelRightRealLinear P.resource (P.decA x y)
      (P.decB x y) (P.instrumentA.branch x))
  obtain ⟨n, hn, select, scale, J, hscale, hops, _, hsum⟩ :=
    P.instrumentB.exists_score_preserving_compression L
  let Q := P.replaceBobInstrument J select
  refine ⟨n, hn, select, scale, Q, hscale, rfl, rfl, hops,
    (fun _ _ => rfl), (fun _ _ => rfl), ?_⟩
  calc
    S Q.operationalChannel = ∑ x, ∑ j,
        S (Q.outcomeChannel x j (Q.instrumentA.branch x) (J.branch j)) := by
      rw [Q.operationalChannel_eq_sum_outcomeChannel]
      simp only [map_sum, Q, replaceBobInstrument]
    _ = ∑ j, ∑ x,
        S (Q.outcomeChannel x j (Q.instrumentA.branch x) (J.branch j)) := Finset.sum_comm
    _ = ∑ j, L (select j) (J.branch j) := by
      simp only [L, LinearMap.sum_apply, LinearMap.comp_apply,
        branchChannelRightRealLinear_apply, Q, replaceBobInstrument, outcomeChannel]
    _ = ∑ y, L y (P.instrumentB.branch y) := hsum
    _ = ∑ y, ∑ x,
        S (P.outcomeChannel x y (P.instrumentA.branch x) (P.instrumentB.branch y)) := by
      simp only [L, LinearMap.sum_apply, LinearMap.comp_apply,
        branchChannelRightRealLinear_apply, outcomeChannel]
    _ = S P.operationalChannel := by
      rw [P.operationalChannel_eq_sum_outcomeChannel]
      simp only [map_sum]
      exact Finset.sum_comm

/-- Two-party finite outcome compression preserves the prescribed score
exactly, with the original resource and every quantum/private register unchanged. -/
theorem exists_finiteOutcome_compression_preserving_linearScore
    [Nonempty ιA] [Nonempty ιB] :
    ∃ nA : ℕ, nA ≤ Fintype.card (ιA × ρA) ^ 2 + 1 ∧
      ∃ nB : ℕ, nB ≤ Fintype.card (ιB × ρB) ^ 2 + 1 ∧
        ∃ Q : FiniteClassicalProtocol ιA ιB ρA ρB κA κB μA μB
          (Fin nA) (Fin nB) ηA ηB ιA' ιB' εA εB,
          Q.resource = P.resource ∧
          (∀ K, Q.HasQuantumFootprint K ↔ P.HasQuantumFootprint K) ∧
          S Q.operationalChannel = S P.operationalChannel := by
  obtain ⟨nA, hnA, selectA, scaleA, A, _, hresourceA, _, _, _, _, hscoreA⟩ :=
    P.exists_compressAlice_preserving_linearScore S
  obtain ⟨nB, hnB, selectB, scaleB, Q, _, hresourceB, _, _, _, _, hscoreB⟩ :=
    A.exists_compressBob_preserving_linearScore S
  have hresource : Q.resource = P.resource := hresourceB.trans hresourceA
  refine ⟨nA, hnA, nB, hnB, Q, hresource, ?_, hscoreB.trans hscoreA⟩
  intro K
  change HasFootprint K Q.resource μA μB ↔ HasFootprint K P.resource μA μB
  rw [hresource]

end NLQCLean.ClassicalCommunication.FiniteClassicalProtocol

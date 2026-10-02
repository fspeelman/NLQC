import NLQCLean.Models.ClassicalCommunication.FiniteProtocol

/-!
# Channel semantics of finite coherent conversion

The copied outcome labels and private Kraus labels are explicitly discarded.
Different classical sectors are orthogonal, so the resulting channel is the
sum of the original unnormalized outcome/Kraus branches.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix
open scoped Kronecker

attribute [local implicit_reducible] Matrix

section ChannelSlices

variable {ι κ ε : Type*} [Fintype ι] [Fintype κ] [Fintype ε]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ε]

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] [DecidableEq ε] in
/-- Partial trace is the sum of the actual environment Kraus slices. -/
theorem channelOf_eq_sum_adConj (F : Matrix (κ × ε) ι ℂ) :
    channelOf F = ∑ e, adConj (sliceAt F e) := by
  apply LinearMap.ext
  intro X
  ext i j
  simp only [channelOf_apply, ptraceB_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, LinearMap.sum_apply, Matrix.sum_apply,
    adConj_apply, sliceAt_apply]

omit [Fintype κ] [Fintype ε]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ε] in
@[simp] theorem adConj_zero : adConj (0 : Matrix κ ι ℂ) = 0 := by
  apply LinearMap.ext
  intro X
  simp [adConj_apply]

end ChannelSlices

private theorem sum_rotate_three {α β γ V : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid V]
    (f : α → β → γ → V) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  exact Finset.sum_comm

private theorem sum_ite_irrel {α V : Type*} [Fintype α] [AddCommMonoid V]
    (p : Prop) [Decidable p] (f : α → V) :
    (∑ a, if p then f a else 0) = if p then ∑ a, f a else 0 := by
  by_cases h : p <;> simp [h]

section Amplitudes

variable {ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]

omit [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
  [DecidableEq ρA] [DecidableEq ρB] [DecidableEq ιA'] [DecidableEq ιB']
  [DecidableEq εA] [DecidableEq εB] in
/-- The actual exchanged amplitude, without normalization hypotheses on the
individual outcome matrices. -/
theorem globalIsometry_entry
    (γ : ρA × ρB → ℂ)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (p : (ιA' × εA) × (ιB' × εB)) (i : ιA × ιB) :
    NLQCLean.globalIsometry γ VA VB DA DB p i =
      ∑ kA, ∑ qB, ∑ kB, ∑ qA,
        (DA p.1 (kA, qB) * DB p.2 (kB, qA)) *
          (∑ rA, ∑ rB,
            (VA (kA, qA) (i.1, rA) * VB (kB, qB) (i.2, rB)) * γ (rA, rB)) := by
  simp [NLQCLean.globalIsometry, decoder, encodedState, exchangeMatrix_mul,
    Matrix.mul_apply, Matrix.kroneckerMap_apply, insertResource_apply,
    Fintype.sum_prod_type, ite_mul, mul_ite, mul_assoc]

end Amplitudes

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

set_option maxHeartbeats 1200000 in
/-- Only matching copies of both classical labels survive. The private Kraus
labels select the original unnormalized branch amplitude exactly. -/
theorem coherentProtocol_globalIsometry_apply
    (a : ιA') (b : ιB') (u : εA) (v : εB)
    (x x' : σA) (y y' : σB) (e : ηA) (f : ηB) (i : ιA × ιB) :
    P.coherentProtocol.globalIsometry
      ((a, (u, (x, (y, e)))), (b, (v, (x', (y', f))))) i =
      if x = x' ∧ y = y' then P.branchAmplitude x y e f ((a, u), (b, v)) i else 0 := by
  change NLQCLean.globalIsometry P.resource P.instrumentA.coherentEncoder
    P.instrumentB.coherentEncoder P.coherentDecoderA P.coherentDecoderB _ i = _
  rw [globalIsometry_entry]
  dsimp only [coherentDecoderA, coherentDecoderB, FiniteKrausInstrument.coherentEncoder,
    Matrix.of_apply]
  unfold branchAmplitude
  generalize P.decA = DA
  generalize P.decB = DB
  conv_lhs => simp (maxSteps := 200000) only [Fintype.sum_prod_type]
  conv_lhs => simp (maxSteps := 200000) only [Prod.mk.injEq, ite_and]
  by_cases h : x = x' ∧ y = y'
  · rw [ite_eq_left h]
    conv_rhs => rw [globalIsometry_entry]
    obtain ⟨rfl, rfl⟩ := h
    simp (maxSteps := 100000) only [ite_mul, apply_ite, sum_ite_irrel,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, zero_mul, mul_zero, ite_eq_left]
  · rw [ite_eq_right h]
    simp (maxSteps := 100000) [ite_mul, apply_ite]
    intro hx hy
    exact (h ⟨hx, hy⟩).elim

/-- Discarding both retained copies and private Kraus labels recovers the
original branch-sum channel exactly, not only its target score. -/
theorem coherentProtocol_operationalChannel :
    P.coherentProtocol.operationalChannel = P.operationalChannel := by
  change channelOf (P.coherentProtocol.globalIsometry.submatrix
    (outputRegroup _ _ _ _) id) = P.operationalChannel
  let G := P.coherentProtocol.globalIsometry.submatrix (outputRegroup _ _ _ _) id
  have hs (u : εA) (v : εB) (x x' : σA) (y y' : σB) (e : ηA) (f : ηB) :
      sliceAt G ((u, (x, (y, e))), (v, (x', (y', f)))) =
        if x = x' ∧ y = y' then
          sliceAt ((P.branchAmplitude x y e f).submatrix
            (outputRegroup ιA' ιB' εA εB) id) (u, v) else 0 := by
    ext a i
    change P.coherentProtocol.globalIsometry
      ((a.1, (u, (x, (y, e)))), (a.2, (v, (x', (y', f))))) i = _
    rw [P.coherentProtocol_globalIsometry_apply]
    split_ifs <;> rfl
  change channelOf G = _
  rw [channelOf_eq_sum_adConj]
  simp only [Fintype.sum_prod_type, hs, apply_ite, adConj_zero, ite_and]
  simp only [sum_ite_irrel, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  unfold operationalChannel
  simp only [channelOf_eq_sum_adConj, Fintype.sum_prod_type]
  rw [sum_rotate_three]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  exact (sum_rotate_three (fun (f : ηB) (u : εA) (v : εB) =>
    adConj (sliceAt ((P.branchAmplitude x y e f).submatrix
      (outputRegroup ιA' ιB' εA εB) id) (u, v)))).symm

end FiniteClassicalProtocol

end NLQCLean.ClassicalCommunication

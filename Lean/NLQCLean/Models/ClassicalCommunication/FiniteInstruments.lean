import NLQCLean.Models.Channels
import NLQCLean.Models.ChannelAmplification
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Finite Kraus instruments

An outcome is a finite Kraus family. The normalization is an operator
identity across all outcomes, so forgetting the outcome gives a
trace-preserving channel. Complete positivity holds for every finite ancilla.

General CP-valued instruments are treated in `CPVectorInstrument`, and
standard-Borel protocols in `StandardBorelProtocol`.
-/

namespace NLQCLean
namespace ClassicalCommunication

open Matrix
open scoped Kronecker ComplexOrder

variable {ι κ σ ε : Type*} [Fintype ι] [Fintype κ] [Fintype σ] [Fintype ε]
variable [DecidableEq ι] [DecidableEq κ]

/-- Complete positivity in the same tensor order as `amplify`. -/
def CompletelyPositive (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) : Prop :=
  ∀ n : ℕ, ∀ X : Matrix (ι × Fin n) (ι × Fin n) ℂ,
    X.PosSemidef → (amplify Φ (Fin n) X).PosSemidef

omit [Fintype κ] [DecidableEq κ] in
/-- Ancilla amplification of one Kraus operator is its tensor extension. -/
theorem amplify_adConj {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix κ ι ℂ) (X : Matrix (ι × α) (ι × α) ℂ) :
    amplify (adConj A) α X =
      (A ⊗ₖ (1 : Matrix α α ℂ)) * X * (A ⊗ₖ (1 : Matrix α α ℂ))ᴴ := by
  ext p q
  simp [amplify_apply, adConj_apply, Matrix.mul_apply, Matrix.single_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, ite_and, Finset.sum_mul, apply_ite, ite_mul,
    mul_comm, mul_left_comm, mul_assoc]
  exact Finset.sum_comm

omit [DecidableEq κ] in
/-- Conjugation by any rectangular matrix is completely positive. -/
theorem completelyPositive_adConj (A : Matrix κ ι ℂ) :
    CompletelyPositive (adConj A) := by
  intro n X hX
  rw [amplify_adConj]
  exact hX.mul_mul_conjTranspose_same _

/-- A finite Kraus family defines a linear operation without a normalization
requirement. -/
def krausMap (A : ε → Matrix κ ι ℂ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ :=
  ∑ e, adConj (A e)

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem krausMap_apply (A : ε → Matrix κ ι ℂ) (X : Matrix ι ι ℂ) :
    krausMap A X = ∑ e, A e * X * (A e)ᴴ := by
  simp [krausMap, adConj_apply]

omit [Fintype κ] [DecidableEq κ] in
theorem amplify_krausMap {α : Type*} [Fintype α] [DecidableEq α]
    (A : ε → Matrix κ ι ℂ) (X : Matrix (ι × α) (ι × α) ℂ) :
    amplify (krausMap A) α X = ∑ e, amplify (adConj (A e)) α X := by
  ext p q
  simp only [amplify_apply, krausMap, LinearMap.sum_apply, Matrix.sum_apply,
    Finset.sum_mul]
  calc
    _ = ∑ i, ∑ e, ∑ j,
        adConj (A e) (Matrix.single i j 1) p.1 q.1 * X (i, p.2) (j, q.2) :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

omit [DecidableEq κ] in
/-- Finite Kraus operations remain positive under every finite amplification. -/
theorem completelyPositive_krausMap (A : ε → Matrix κ ι ℂ) :
    CompletelyPositive (krausMap A) := by
  intro n X hX
  rw [amplify_krausMap]
  exact Matrix.posSemidef_sum _ (fun e _ => completelyPositive_adConj (A e) n X hX)

/-- A finite-outcome instrument, with an explicit finite Kraus index in every
branch and an actual trace-preserving normalization. -/
structure FiniteKrausInstrument (ι κ σ ε : Type*)
    [Fintype ι] [Fintype κ] [Fintype σ] [Fintype ε] [DecidableEq ι] where
  operator : σ → ε → Matrix κ ι ℂ
  normalized : ∑ x, ∑ e, (operator x e)ᴴ * operator x e = 1

namespace FiniteKrausInstrument

variable (I : FiniteKrausInstrument ι κ σ ε)

/-- The completely positive operation belonging to an actual outcome. -/
def branch (x : σ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ := krausMap (I.operator x)

omit [DecidableEq κ] in
theorem branch_completelyPositive (x : σ) : CompletelyPositive (I.branch x) :=
  completelyPositive_krausMap _

/-- Discard the classical outcome, summing its unnormalized operations. -/
def channel : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ := ∑ x, I.branch x

omit [DecidableEq κ] in
@[simp] theorem channel_apply (X : Matrix ι ι ℂ) :
    I.channel X = ∑ x, ∑ e, I.operator x e * X * (I.operator x e)ᴴ := by
  simp [channel, branch]

omit [DecidableEq κ] in
/-- Forgetting labels still gives a completely positive map, with the actual
outcome and Kraus labels as one finite Kraus index. -/
theorem channel_completelyPositive : CompletelyPositive I.channel := by
  have h : I.channel = krausMap (fun p : σ × ε => I.operator p.1 p.2) := by
    ext X i j
    simp only [channel_apply, krausMap_apply, Fintype.sum_prod_type, Matrix.sum_apply]
  rw [h]
  exact completelyPositive_krausMap _

omit [DecidableEq κ] in
/-- Instrument normalization preserves the trace for every matrix, not only
positive states. -/
theorem trace_channel (X : Matrix ι ι ℂ) : trace (I.channel X) = trace X := by
  rw [channel_apply, Matrix.trace_sum]
  simp only [Matrix.trace_sum]
  calc
    _ = ∑ x, ∑ e, trace ((I.operator x e)ᴴ * I.operator x e * X) := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_congr rfl (fun e _ => Matrix.trace_mul_cycle _ _ _)
    _ = trace ((∑ x, ∑ e, (I.operator x e)ᴴ * I.operator x e) * X) := by
      simp only [Matrix.sum_mul, Matrix.trace_sum]
    _ = trace X := by rw [I.normalized, Matrix.one_mul]

/-- The actual finite Stinespring matrix, retaining outcome and Kraus labels
in its environment. -/
def dilation : Matrix (κ × (σ × ε)) ι ℂ :=
  fun p i => I.operator p.2.1 p.2.2 p.1 i

omit [DecidableEq κ] in
/-- The instrument normalization makes its Stinespring matrix an isometry. -/
theorem dilation_isometry : IsIsometry I.dilation := by
  ext i j
  have h := congrArg (fun M : Matrix ι ι ℂ => M i j) I.normalized
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply] at h
  simp only [dilation, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]
  calc
    _ = ∑ x, ∑ e, ∑ k, star (I.operator x e k i) * I.operator x e k j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = _ := h

omit [DecidableEq κ] in
/-- Forgetting actual outcome/Kraus labels agrees with the existing physical
channel construction. -/
theorem channel_eq_channelOf_dilation : I.channel = channelOf I.dilation := by
  ext X i j
  rw [channel_apply, channelOf_apply]
  simp only [ptraceB_apply, dilation, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Finset.sum_mul]

/-- One classical outcome and a single isometry recover the ordinary channel. -/
def ofIsometry (A : Matrix κ ι ℂ) (hA : IsIsometry A) :
    FiniteKrausInstrument ι κ Unit Unit where
  operator := fun _ _ => A
  normalized := by simpa using hA.conjTranspose_mul_self

omit [DecidableEq κ] in
@[simp] theorem channel_ofIsometry (A : Matrix κ ι ℂ) (hA : IsIsometry A) :
    (ofIsometry A hA).channel = adConj A := by
  ext X p q
  simp [channel_apply, ofIsometry, adConj_apply]

omit [DecidableEq κ] in
/-- Every existing purified channel is a one-outcome instrument, with its
actual environment indices as Kraus labels. -/
def ofStinespring (A : Matrix (κ × ε) ι ℂ) (hA : IsIsometry A) :
    FiniteKrausInstrument ι κ Unit ε where
  operator := fun _ e k i => A (k, e) i
  normalized := by
    ext i j
    have h := congrArg (fun M : Matrix ι ι ℂ => M i j) hA.conjTranspose_mul_self
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type] at h
    simp only [Matrix.sum_apply, Fintype.sum_unique]
    exact Finset.sum_comm.trans h

omit [DecidableEq κ] in
@[simp] theorem channel_ofStinespring (A : Matrix (κ × ε) ι ℂ) (hA : IsIsometry A) :
    (ofStinespring A hA).channel = channelOf A := by
  ext X i j
  simp only [channel_apply, ofStinespring, Fintype.sum_unique, channelOf_apply,
    ptraceB_apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rfl

end FiniteKrausInstrument

/-- Coherently copy a finite classical basis label into kept and sent labels. -/
def copyLabel (σ : Type*) [DecidableEq σ] : Matrix (σ × σ) σ ℂ :=
  fun p x => if p.1 = x ∧ p.2 = x then 1 else 0

theorem copyLabel_isometry (σ : Type*) [Fintype σ] [DecidableEq σ] :
    IsIsometry (copyLabel σ) := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [copyLabel, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, apply_ite, ite_and]
  · simp [copyLabel, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, apply_ite, ite_and, hxy, Ne.symm hxy]

omit [Fintype σ] in
@[simp] theorem copyLabel_diagonal (x : σ) [DecidableEq σ] :
    copyLabel σ (x, x) x = 1 := by simp [copyLabel]

omit [Fintype σ] in
theorem copyLabel_off_diagonal (x y z : σ) [DecidableEq σ] (hxy : x ≠ y) :
    copyLabel σ (x, y) z = 0 := by
  simp only [copyLabel]
  split_ifs with h
  · exact (hxy (h.1.trans h.2.symm)).elim
  · rfl

end ClassicalCommunication
end NLQCLean

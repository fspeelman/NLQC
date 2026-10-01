import NLQCLean.Exact.SpectatorControlledPhase
import NLQCLean.Exact.LocalChannelRestriction
import Mathlib.Data.Fin.Tuple.Basic

/-!
# The first-qubit controlled phase on bitstrings

A bitstring of positive length is its head qubit and remaining spectators.
The basis equivalence gives the exact source gate and actual local restriction
channels, with the first bit represented by index zero.
-/

noncomputable section

namespace NLQCLean

open Matrix ClassicalCommunication
open scoped Kronecker

abbrev QubitString (n : ℕ) := Fin n → Fin 2

/-- Separate the first qubit from every remaining bit, including no remaining bits. -/
def qubitStringHeadEquiv (k : ℕ) : Fin 2 × QubitString k ≃ QubitString (k + 1) :=
  Fin.consEquiv (fun _ => Fin 2)

/-- The source gate on `k + 1` qubits per party, acting only on the first bits. -/
def bitstringControlledPhase (k : ℕ) (θ : ℝ) :
    Matrix (QubitString (k + 1) × QubitString (k + 1))
      (QubitString (k + 1) × QubitString (k + 1)) ℂ :=
  (spectatorControlledPhase (σA := QubitString k) (σB := QubitString k) θ).submatrix
    ((qubitStringHeadEquiv k).symm.prodCongr (qubitStringHeadEquiv k).symm)
    ((qubitStringHeadEquiv k).symm.prodCongr (qubitStringHeadEquiv k).symm)

/-- Entry formula for the first-bit source target. -/
theorem bitstringControlledPhase_apply (k : ℕ) (θ : ℝ)
    (p q : QubitString (k + 1) × QubitString (k + 1)) :
    bitstringControlledPhase k θ p q =
      if p = q then (if p.1 0 = 1 ∧ p.2 0 = 1 then
        Complex.exp ((θ : ℂ) * Complex.I) else 1) else 0 := by
  change (if ((qubitStringHeadEquiv k).symm.prodCongr (qubitStringHeadEquiv k).symm) p =
      ((qubitStringHeadEquiv k).symm.prodCongr (qubitStringHeadEquiv k).symm) q then
      (if p.1 0 = 1 ∧ p.2 0 = 1 then Complex.exp ((θ : ℂ) * Complex.I) else 1) else 0) = _
  simp only [Equiv.apply_eq_iff_eq]

/-- The local dimension is exactly the source power of two. -/
theorem card_qubitString (n : ℕ) : Fintype.card (QubitString n) = 2 ^ n := by
  simp [QubitString]

/-- The source exponential formula with both first bits as integer exponents. -/
theorem bitstringControlledPhase_source_apply (k : ℕ) (θ : ℝ)
    (p q : QubitString (k + 1) × QubitString (k + 1)) :
    bitstringControlledPhase k θ p q =
      if p = q then Complex.exp
        (((θ : ℂ) * (p.1 0).val * (p.2 0).val) * Complex.I) else 0 := by
  rw [bitstringControlledPhase_apply]
  by_cases hpq : p = q
  · simp only [hpq, if_true]
    generalize ha : p.1 0 = a
    generalize hb : p.2 0 = b
    fin_cases a <;> fin_cases b <;> simp_all
  · simp only [hpq, if_false]

/-- The source bitstring gate is unitary at every real angle. -/
theorem bitstringControlledPhase_unitary (k : ℕ) (θ : ℝ) :
    (bitstringControlledPhase k θ)ᴴ * bitstringControlledPhase k θ = 1 ∧
      bitstringControlledPhase k θ * (bitstringControlledPhase k θ)ᴴ = 1 := by
  let e := (qubitStringHeadEquiv k).symm.prodCongr (qubitStringHeadEquiv k).symm
  have h := spectatorControlledPhase_unitary (σA := QubitString k) (σB := QubitString k) θ
  change ((spectatorControlledPhase θ).submatrix e e)ᴴ *
      (spectatorControlledPhase θ).submatrix e e = 1 ∧
    (spectatorControlledPhase θ).submatrix e e *
      ((spectatorControlledPhase θ).submatrix e e)ᴴ = 1
  simp only [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  constructor
  · rw [h.1, Matrix.submatrix_one_equiv]
  · rw [h.2, Matrix.submatrix_one_equiv]

def bitstringInputIsometry (k : ℕ) : Matrix (QubitString (k + 1)) (Fin 2) ℂ :=
  (spectatorInputIsometry (fun _ : Fin k => (0 : Fin 2))).submatrix
    (qubitStringHeadEquiv k).symm id

def bitstringOutputStinespring (k : ℕ) :
    Matrix (Fin 2 × QubitString k) (QubitString (k + 1)) ℂ :=
  (spectatorOutputStinespring (QubitString k)).submatrix id (qubitStringHeadEquiv k).symm

theorem bitstringInputIsometry_isometry (k : ℕ) : IsIsometry (bitstringInputIsometry k) :=
  (spectatorInputIsometry_isometry _).submatrix_equiv
    (qubitStringHeadEquiv k).symm (Equiv.refl _)

theorem bitstringOutputStinespring_isometry (k : ℕ) :
    IsIsometry (bitstringOutputStinespring k) :=
  (spectatorOutputStinespring_isometry _).submatrix_equiv
    (Equiv.refl _) (qubitStringHeadEquiv k).symm

/-- Exact ideal-channel restriction, retaining all discarded spectator bits. -/
theorem bitstringControlledPhase_restrictedChannel_eq (k : ℕ) (θ : ℝ) :
    localChannelRestriction (bitstringInputIsometry k) (bitstringInputIsometry k)
      (bitstringOutputStinespring k) (bitstringOutputStinespring k)
      (bitstringControlledPhase k θ) = adConj (controlledPhase θ) := by
  rw [bitstringInputIsometry, bitstringOutputStinespring, bitstringControlledPhase,
    localChannelRestriction_reindex]
  exact spectatorControlledPhase_restrictedChannel_eq θ
    (fun _ : Fin k => (0 : Fin 2)) (fun _ : Fin k => (0 : Fin 2))

end NLQCLean

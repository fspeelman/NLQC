import NLQCLean.Rigidity.FlaggedSupports
import NLQCLean.Approx.PVMRankAllocations
import NLQCLean.Models.PVMForwardCompression
import NLQCLean.Approx.PVMSharpFreezing
import NLQCLean.Approx.ReverseWitness

/-!
# Compressed physical reverse witnesses for rank-one PVMs

The reverse domain is the flagged direct sum of the selected
Schmidt supports. Each contraction is completed in a row space of dimension
dK+S, fixed by the charged architecture and rank allocation. No physical
environment dimension or smoothly chosen support appears in that shape.
-/

namespace NLQCLean
open Matrix
open scoped Matrix.Norms.Frobenius Kronecker MatrixOrder ComplexOrder

/-- Exact wiring of completed reverse maps through arbitrary local support
inclusions. The support identity is discharged by the physical flagged
Schmidt factorizations below. -/
theorem pvm_reverse_crossGram_overlap
    {i a b qA qB gA gB lA lB : Type*}
    [Fintype i] [Fintype a] [Fintype b] [Fintype qA] [Fintype qB]
    [Fintype gA] [Fintype gB] [Fintype lA] [Fintype lB]
    (Y : Matrix (qA × qB) i ℂ)
    (WA : Matrix a qA ℂ) (WB : Matrix b qB ℂ)
    (JA : Matrix a gA ℂ) (JB : Matrix b gB ℂ)
    (EA : Matrix lA qA ℂ) (EB : Matrix lB qB ℂ)
    (TA : Matrix lA gA ℂ) (TB : Matrix lB gB ℂ)
    (G : Matrix (gA × gB) i ℂ) (C : Matrix (a × b) i ℂ)
    (hA : EAᴴ * TA = WAᴴ * JA) (hB : EBᴴ * TB = WBᴴ * JB)
    (hC : (JA ⊗ₖ JB) * G = C) :
    ((TA ⊗ₖ TB) * G)ᴴ * ((EA ⊗ₖ EB) * Y) = Cᴴ * ((WA ⊗ₖ WB) * Y) := by
  have ha : TAᴴ * EA = JAᴴ * WA := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
      congrArg Matrix.conjTranspose hA
  have hb : TBᴴ * EB = JBᴴ * WB := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
      congrArg Matrix.conjTranspose hB
  have htop : (TA ⊗ₖ TB)ᴴ * (EA ⊗ₖ EB) = (JA ⊗ₖ JB)ᴴ * (WA ⊗ₖ WB) := by
    simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ha, hb]
  calc
    _ = Gᴴ * ((TA ⊗ₖ TB)ᴴ * (EA ⊗ₖ EB)) * Y := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Gᴴ * ((JA ⊗ₖ JB)ᴴ * (WA ⊗ₖ WB)) * Y := by rw [htop]
    _ = ((JA ⊗ₖ JB) * G)ᴴ * ((WA ⊗ₖ WB) * Y) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hC]

namespace PVMReverseShape
variable {d K : ℕ} (s : PVMReverseShape d K)

/-- Sum of the chosen flag-support dimensions, charged once over all labels. -/
def supportSize : ℕ := ∑ i, s.2.rank i

abbrev Support := FlagSupport s.2.rank

theorem card_support : Fintype.card s.Support = s.supportSize := by
  simp [Support, FlagSupport, supportSize, Fintype.card_sigma]

theorem completion_rowsA :
    Fintype.card (Fin (d * s.1.r * s.1.mA) × Fin s.1.mB) +
      Fintype.card s.Support ≤ d * K + s.supportSize := by
  rw [s.card_support]
  simp only [Fintype.card_prod, Fintype.card_fin]
  have h : d * s.1.r * s.1.mA * s.1.mB ≤ d * K := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left d s.1.footprint
  exact Nat.add_le_add_right h _

theorem completion_rowsB :
    Fintype.card (Fin (d * s.1.r * s.1.mB) × Fin s.1.mA) +
      Fintype.card s.Support ≤ d * K + s.supportSize := by
  rw [s.card_support]
  simp only [Fintype.card_prod, Fintype.card_fin]
  have h : d * s.1.r * s.1.mB * s.1.mA ≤ d * K := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_left d s.1.footprint
  exact Nat.add_le_add_right h _

/-- Row inclusions are fixed by the shape before choosing any witness blocks. -/
noncomputable def rowEmbeddingA :
    Matrix (Fin (d * K + s.supportSize)) (Fin (d * s.1.r * s.1.mA) × Fin s.1.mB) ℂ :=
  Classical.choose (exists_uniform_isometric_completion_with_rows
    (Fin (d * s.1.r * s.1.mA) × Fin s.1.mB) s.Support (d * K + s.supportSize)
    s.completion_rowsA)

noncomputable def rowEmbeddingB :
    Matrix (Fin (d * K + s.supportSize)) (Fin (d * s.1.r * s.1.mB) × Fin s.1.mA) ℂ :=
  Classical.choose (exists_uniform_isometric_completion_with_rows
    (Fin (d * s.1.r * s.1.mB) × Fin s.1.mA) s.Support (d * K + s.supportSize)
    s.completion_rowsB)

theorem isIsometry_rowEmbeddingA : IsIsometry s.rowEmbeddingA :=
  (Classical.choose_spec (exists_uniform_isometric_completion_with_rows
    (Fin (d * s.1.r * s.1.mA) × Fin s.1.mB) s.Support (d * K + s.supportSize)
    s.completion_rowsA)).1

theorem isIsometry_rowEmbeddingB : IsIsometry s.rowEmbeddingB :=
  (Classical.choose_spec (exists_uniform_isometric_completion_with_rows
    (Fin (d * s.1.r * s.1.mB) × Fin s.1.mA) s.Support (d * K + s.supportSize)
    s.completion_rowsB)).1

theorem completeA
    (C : Matrix (Fin (d * s.1.r * s.1.mA) × Fin s.1.mB) s.Support ℂ)
    (hC : (1 - Cᴴ * C).PosSemidef) :
    ∃ T : Matrix (Fin (d * K + s.supportSize)) s.Support ℂ,
      IsIsometry T ∧ s.rowEmbeddingAᴴ * T = C :=
  (Classical.choose_spec (exists_uniform_isometric_completion_with_rows
    (Fin (d * s.1.r * s.1.mA) × Fin s.1.mB) s.Support (d * K + s.supportSize)
    s.completion_rowsA)).2 C hC

theorem completeB
    (C : Matrix (Fin (d * s.1.r * s.1.mB) × Fin s.1.mA) s.Support ℂ)
    (hC : (1 - Cᴴ * C).PosSemidef) :
    ∃ T : Matrix (Fin (d * K + s.supportSize)) s.Support ℂ,
      IsIsometry T ∧ s.rowEmbeddingBᴴ * T = C :=
  (Classical.choose_spec (exists_uniform_isometric_completion_with_rows
    (Fin (d * s.1.r * s.1.mB) × Fin s.1.mA) s.Support (d * K + s.supportSize)
    s.completion_rowsB)).2 C hC

end PVMReverseShape

/-- The resource, per-label garbage, two encoders and two reverse isometries
are the six independent blocks. The garbage block has sum_i s_i² entries. -/
abbrev PVMReverseBlocks {d K : ℕ} (s : PVMReverseShape d K) :=
  (Fin s.1.r × Fin s.1.r → ℂ) ×
  ((i : Fin d × Fin d) → Fin (s.2.rank i) × Fin (s.2.rank i) → ℂ) ×
  Matrix (Fin (d * s.1.r * s.1.mA) × Fin s.1.mA) (Fin d × Fin s.1.r) ℂ ×
  Matrix (Fin (d * s.1.r * s.1.mB) × Fin s.1.mB) (Fin d × Fin s.1.r) ℂ ×
  Matrix (Fin (d * K + s.supportSize)) s.Support ℂ ×
  Matrix (Fin (d * K + s.supportSize)) s.Support ℂ

namespace PVMReverseBlocks
variable {d K : ℕ} {s : PVMReverseShape d K}

def IsValid (x : PVMReverseBlocks s) : Prop :=
  IsUnitVector x.1 ∧ (∀ i, IsUnitVector (x.2.1 i)) ∧ IsIsometry x.2.2.1 ∧
    IsIsometry x.2.2.2.1 ∧ IsIsometry x.2.2.2.2.1 ∧ IsIsometry x.2.2.2.2.2

noncomputable def forward (x : PVMReverseBlocks s) :
    Matrix (Fin (d * K + s.supportSize) × Fin (d * K + s.supportSize)) (Fin d × Fin d) ℂ :=
  (s.rowEmbeddingA ⊗ₖ s.rowEmbeddingB) * encodedState x.1 x.2.2.1 x.2.2.2.1

noncomputable def reverse (x : PVMReverseBlocks s) :
    Matrix (Fin (d * K + s.supportSize) × Fin (d * K + s.supportSize)) (Fin d × Fin d) ℂ :=
  (x.2.2.2.2.1 ⊗ₖ x.2.2.2.2.2) * compressedFlag x.2.1

noncomputable def overlap (x : PVMReverseBlocks s) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (reverse x)ᴴ * forward x

theorem IsValid.isIsometry_forward {x : PVMReverseBlocks s} (hx : IsValid x) :
    IsIsometry (forward x) :=
  (s.isIsometry_rowEmbeddingA.kronecker s.isIsometry_rowEmbeddingB).mul
    (isIsometry_encodedState hx.1 hx.2.2.1 hx.2.2.2.1)

theorem IsValid.isIsometry_reverse {x : PVMReverseBlocks s} (hx : IsValid x) :
    IsIsometry (reverse x) :=
  (hx.2.2.2.2.1.kronecker hx.2.2.2.2.2).mul (isIsometry_compressedFlag _ hx.2.1)

/-- The same cross-Gram and leakage identities apply to the PVM
witness isometries; the analysis target is M†. -/
theorem IsValid.approximation {x : PVMReverseBlocks s} (hx : IsValid x)
    (T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    {η : ℝ} (hη : 0 ≤ η) (hclose : ‖forward x - reverse x * T‖ ≤ η) :
    ‖overlap x - T‖ ≤ η ∧
      ‖forward x - reverse x * overlap x‖ ^ 2 = (d : ℝ) ^ 2 - ‖overlap x‖ ^ 2 ∧
      ‖reverse x - forward x * (overlap x)ᴴ‖ ^ 2 = (d : ℝ) ^ 2 - ‖overlap x‖ ^ 2 ∧
      (d : ℝ) ^ 2 - ‖overlap x‖ ^ 2 ≤ η ^ 2 := by
  have h := crossGram_approximation (forward x) (reverse x) T
    hx.isIsometry_forward hx.isIsometry_reverse hη hclose
  simpa only [overlap, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two] using h

end PVMReverseBlocks
end NLQCLean

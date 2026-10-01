import NLQCLean.LinearAlgebra.IsometricCompletion
import NLQCLean.Approx.CrossGramDistance
import NLQCLean.Models.ForwardCompression
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Bounded six-block reverse witnesses

Exact support compression and zero padding produce
backward contractions, completed in fixed row spaces. The final witnesses
use only two unit vectors and four isometric matrix blocks.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker MatrixOrder ComplexOrder

/-- Express a bounded-Schmidt-rank unit vector on exactly K local coordinates.
The maps back to the original environments are contractions; zero padding
therefore requires no enlargement of the physical environment types. -/
theorem exists_padded_resource_support {a b : Type*}
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (v : a × b → ℂ) (hv : IsUnitVector v) {K : ℕ} (hK : schmidtRank v ≤ K) :
    ∃ JA : Matrix a (Fin K) ℂ, ∃ JB : Matrix b (Fin K) ℂ,
      ∃ g : Fin K × Fin K → ℂ,
        IsUnitVector g ∧ (1 - JAᴴ * JA).PosSemidef ∧ (1 - JBᴴ * JB).PosSemidef ∧
          v = (JA ⊗ₖ JB) *ᵥ g := by
  obtain ⟨LA, LB, u, hLA, hLB, hu, hvu⟩ := exists_resource_support_factorization v hv
  obtain ⟨S, hS⟩ := exists_isometry_of_card_le
    (m := Fin (schmidtRank v)) (n := Fin K) (by simpa using hK)
  have hSdef : (1 - Sᴴᴴ * Sᴴ).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hS.posSemidef_one_sub_mul_adjoint
  refine ⟨LA * Sᴴ, LB * Sᴴ, (S ⊗ₖ S) *ᵥ u,
    ((hS.kronecker hS).isUnitVector_mulVec_iff u).mpr hu,
    posSemidef_gram_defect_mul LA Sᴴ hLA.posSemidef_gram_defect hSdef,
    posSemidef_gram_defect_mul LB Sᴴ hLB.posSemidef_gram_defect hSdef, ?_⟩
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul]
  simpa only [Matrix.mul_assoc, hS.conjTranspose_mul_self, Matrix.mul_one] using hvu

/-- Tensoring a contraction with a logical identity preserves its Gram defect. -/
theorem posSemidef_identity_kronecker_defect {a m n : Type*}
    [Fintype a] [Fintype m] [Fintype n] [DecidableEq a] [DecidableEq n]
    (J : Matrix m n ℂ) (hJ : (1 - Jᴴ * J).PosSemidef) :
    (1 - ((1 : Matrix a a ℂ) ⊗ₖ J)ᴴ * ((1 : Matrix a a ℂ) ⊗ₖ J)).PosSemidef := by
  have h := (Matrix.PosSemidef.one : (1 : Matrix a a ℂ).PosSemidef).kronecker hJ
  have hd : (1 : Matrix a a ℂ) ⊗ₖ (1 - Jᴴ * J) =
      1 - (1 : Matrix a a ℂ) ⊗ₖ (Jᴴ * J) := by
    rw [← Matrix.one_kronecker_one]
    ext x y
    simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply, mul_sub]
  simpa only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, hd] using h

/-- W:overlap as an exact wiring identity. Completed reverse blocks recover
the backward decoder contractions on the embedded forward row space. -/
theorem reverse_crossGram_overlap {i a b qA qB eA eB gA gB lA lB : Type*}
    [Fintype i] [Fintype a] [Fintype b] [Fintype qA] [Fintype qB]
    [Fintype eA] [Fintype eB] [Fintype gA] [Fintype gB] [Fintype lA] [Fintype lB]
    [DecidableEq a] [DecidableEq b]
    (Y : Matrix (qA × qB) i ℂ)
    (WA : Matrix (a × eA) qA ℂ) (WB : Matrix (b × eB) qB ℂ)
    (JA : Matrix eA gA ℂ) (JB : Matrix eB gB ℂ)
    (EA : Matrix lA qA ℂ) (EB : Matrix lB qB ℂ)
    (TA : Matrix lA (a × gA) ℂ) (TB : Matrix lB (b × gB) ℂ)
    (g : gA × gB → ℂ) (v : eA × eB → ℂ)
    (hA : EAᴴ * TA = WAᴴ * ((1 : Matrix a a ℂ) ⊗ₖ JA))
    (hB : EBᴴ * TB = WBᴴ * ((1 : Matrix b b ℂ) ⊗ₖ JB))
    (hv : v = (JA ⊗ₖ JB) *ᵥ g) :
    ((TA ⊗ₖ TB) * insertResource a b g)ᴴ * ((EA ⊗ₖ EB) * Y) =
      (insertResource a b v)ᴴ * ((WA ⊗ₖ WB) * Y) := by
  classical
  have ha : TAᴴ * EA = ((1 : Matrix a a ℂ) ⊗ₖ JA)ᴴ * WA := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
      congrArg Matrix.conjTranspose hA
  have hb : TBᴴ * EB = ((1 : Matrix b b ℂ) ⊗ₖ JB)ᴴ * WB := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
      congrArg Matrix.conjTranspose hB
  let J := ((1 : Matrix a a ℂ) ⊗ₖ JA) ⊗ₖ ((1 : Matrix b b ℂ) ⊗ₖ JB)
  have htop : (TA ⊗ₖ TB)ᴴ * (EA ⊗ₖ EB) = Jᴴ * (WA ⊗ₖ WB) := by
    simp only [J, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ha, hb]
  have hsupport : J * insertResource a b g = insertResource a b v := by
    rw [hv, insertResource_tensor_mulVec]
  calc
    _ = (insertResource a b g)ᴴ * ((TA ⊗ₖ TB)ᴴ * (EA ⊗ₖ EB)) * Y := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (insertResource a b g)ᴴ * (Jᴴ * (WA ⊗ₖ WB)) * Y := by rw [htop]
    _ = (J * insertResource a b g)ᴴ * ((WA ⊗ₖ WB) * Y) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hsupport]

/-- The only discrete choices in a reverse-witness family: the resource
rank and two complete message dimensions, all positive and charged. -/
structure ReverseShape (d K : ℕ) where
  r : ℕ
  mA : ℕ
  mB : ℕ
  resource_pos : 0 < r
  messageA_pos : 0 < mA
  messageB_pos : 0 < mB
  footprint : r * mA * mB ≤ K

namespace ReverseShape

variable {d K : ℕ} (s : ReverseShape d K)

theorem completion_rowsA :
    Fintype.card (Fin (d * s.r * s.mA) × Fin s.mB) +
      Fintype.card (Fin d × Fin K) ≤ 2 * d * K := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  have h : d * s.r * s.mA * s.mB ≤ d * K := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left d s.footprint
  nlinarith

theorem completion_rowsB :
    Fintype.card (Fin (d * s.r * s.mB) × Fin s.mA) +
      Fintype.card (Fin d × Fin K) ≤ 2 * d * K := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  have h : d * s.r * s.mB * s.mA ≤ d * K := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_left d s.footprint
  nlinarith

/-- This embedding is fixed by the shape, before the target or six blocks. -/
noncomputable def rowEmbeddingA :
    Matrix (Fin (2 * d * K)) (Fin (d * s.r * s.mA) × Fin s.mB) ℂ :=
  Classical.choose (exists_uniform_isometric_completion_with_rows
    (Fin (d * s.r * s.mA) × Fin s.mB) (Fin d × Fin K) (2 * d * K) s.completion_rowsA)

noncomputable def rowEmbeddingB :
    Matrix (Fin (2 * d * K)) (Fin (d * s.r * s.mB) × Fin s.mA) ℂ :=
  Classical.choose (exists_uniform_isometric_completion_with_rows
    (Fin (d * s.r * s.mB) × Fin s.mA) (Fin d × Fin K) (2 * d * K) s.completion_rowsB)

theorem isIsometry_rowEmbeddingA : IsIsometry s.rowEmbeddingA :=
  (Classical.choose_spec (exists_uniform_isometric_completion_with_rows
    (Fin (d * s.r * s.mA) × Fin s.mB) (Fin d × Fin K) (2 * d * K) s.completion_rowsA)).1

theorem isIsometry_rowEmbeddingB : IsIsometry s.rowEmbeddingB :=
  (Classical.choose_spec (exists_uniform_isometric_completion_with_rows
    (Fin (d * s.r * s.mB) × Fin s.mA) (Fin d × Fin K) (2 * d * K) s.completion_rowsB)).1

theorem completeA (C : Matrix (Fin (d * s.r * s.mA) × Fin s.mB) (Fin d × Fin K) ℂ)
    (hC : (1 - Cᴴ * C).PosSemidef) :
    ∃ T : Matrix (Fin (2 * d * K)) (Fin d × Fin K) ℂ,
      IsIsometry T ∧ s.rowEmbeddingAᴴ * T = C :=
  (Classical.choose_spec (exists_uniform_isometric_completion_with_rows
    (Fin (d * s.r * s.mA) × Fin s.mB) (Fin d × Fin K) (2 * d * K) s.completion_rowsA)).2 C hC

theorem completeB (C : Matrix (Fin (d * s.r * s.mB) × Fin s.mA) (Fin d × Fin K) ℂ)
    (hC : (1 - Cᴴ * C).PosSemidef) :
    ∃ T : Matrix (Fin (2 * d * K)) (Fin d × Fin K) ℂ,
      IsIsometry T ∧ s.rowEmbeddingBᴴ * T = C :=
  (Classical.choose_spec (exists_uniform_isometric_completion_with_rows
    (Fin (d * s.r * s.mB) × Fin s.mA) (Fin d × Fin K) (2 * d * K) s.completion_rowsB)).2 C hC

end ReverseShape

/-- Exactly six independent complex blocks: resource, frozen environment,
two forward encoders, and two completed reverse isometries. -/
abbrev ReverseBlocks {d K : ℕ} (s : ReverseShape d K) :=
  (Fin s.r × Fin s.r → ℂ) × (Fin K × Fin K → ℂ) ×
    Matrix (Fin (d * s.r * s.mA) × Fin s.mA) (Fin d × Fin s.r) ℂ ×
    Matrix (Fin (d * s.r * s.mB) × Fin s.mB) (Fin d × Fin s.r) ℂ ×
    Matrix (Fin (2 * d * K)) (Fin d × Fin K) ℂ ×
    Matrix (Fin (2 * d * K)) (Fin d × Fin K) ℂ

namespace ReverseBlocks

variable {d K : ℕ} {s : ReverseShape d K}

def IsValid (x : ReverseBlocks s) : Prop :=
  IsUnitVector x.1 ∧ IsUnitVector x.2.1 ∧ IsIsometry x.2.2.1 ∧
    IsIsometry x.2.2.2.1 ∧ IsIsometry x.2.2.2.2.1 ∧ IsIsometry x.2.2.2.2.2

noncomputable def forward (x : ReverseBlocks s) :
    Matrix (Fin (2 * d * K) × Fin (2 * d * K)) (Fin d × Fin d) ℂ :=
  (s.rowEmbeddingA ⊗ₖ s.rowEmbeddingB) * encodedState x.1 x.2.2.1 x.2.2.2.1

def reverse (x : ReverseBlocks s) :
    Matrix (Fin (2 * d * K) × Fin (2 * d * K)) (Fin d × Fin d) ℂ :=
  (x.2.2.2.2.1 ⊗ₖ x.2.2.2.2.2) * insertResource (Fin d) (Fin d) x.2.1

noncomputable def overlap (x : ReverseBlocks s) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (reverse x)ᴴ * forward x

theorem IsValid.isIsometry_forward {x : ReverseBlocks s} (hx : IsValid x) :
    IsIsometry (forward x) :=
  (s.isIsometry_rowEmbeddingA.kronecker s.isIsometry_rowEmbeddingB).mul
    (isIsometry_encodedState hx.1 hx.2.2.1 hx.2.2.2.1)

theorem IsValid.isIsometry_reverse {x : ReverseBlocks s} (hx : IsValid x) :
    IsIsometry (reverse x) :=
  (hx.2.2.2.2.1.kronecker hx.2.2.2.2.2).mul (isIsometry_insertResource _ hx.2.1)

/-- The exact leakage identities apply to every valid six-block witness. -/
theorem IsValid.approximation {x : ReverseBlocks s} (hx : IsValid x)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    {η : ℝ} (hη : 0 ≤ η) (hclose : ‖forward x - reverse x * U‖ ≤ η) :
    ‖overlap x - U‖ ≤ η ∧
      ‖forward x - reverse x * overlap x‖ ^ 2 = (d : ℝ) ^ 2 - ‖overlap x‖ ^ 2 ∧
      ‖reverse x - forward x * (overlap x)ᴴ‖ ^ 2 = (d : ℝ) ^ 2 - ‖overlap x‖ ^ 2 ∧
      (d : ℝ) ^ 2 - ‖overlap x‖ ^ 2 ≤ η ^ 2 := by
  have h := crossGram_approximation (forward x) (reverse x) U
    hx.isIsometry_forward hx.isIsometry_reverse hη hclose
  simpa only [overlap, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two] using h

end ReverseBlocks

/-- W:compress--W:overlap after resource and private-register compression.
Encoder rows are padded to the shape's fixed sizes. The given physical
rank-K environment is represented exactly, and completion absorbs the
backward contractions into the last two of the six independent blocks. -/
theorem PureProtocol.exists_reverse_blocks_of_frozen
    {d K kA kB : ℕ} (s : ReverseShape d K) {eA eB : Type*}
    [Fintype eA] [Fintype eB] [DecidableEq eA] [DecidableEq eB]
    (P : PureProtocol (Fin d) (Fin d) (Fin s.r) (Fin s.r) (Fin kA) (Fin kB)
      (Fin s.mA) (Fin s.mB) (Fin d) (Fin d) eA eB)
    (hkA : kA ≤ d * s.r * s.mA) (hkB : kB ≤ d * s.r * s.mB)
    (v : eA × eB → ℂ) (hv : IsUnitVector v) (hvrank : schmidtRank v ≤ K) :
    ∃ x : ReverseBlocks s, ReverseBlocks.IsValid x ∧
      ReverseBlocks.overlap x = (insertResource (Fin d) (Fin d) v)ᴴ * P.globalIsometry := by
  obtain ⟨PA, hPA⟩ := exists_isometry_of_card_le
    (m := Fin kA) (n := Fin (d * s.r * s.mA)) (by simpa using hkA)
  obtain ⟨PB, hPB⟩ := exists_isometry_of_card_le
    (m := Fin kB) (n := Fin (d * s.r * s.mB)) (by simpa using hkB)
  obtain ⟨JA, JB, g, hg, hJA, hJB, hvrep⟩ := exists_padded_resource_support v hv hvrank
  let QA := PA ⊗ₖ (1 : Matrix (Fin s.mB) (Fin s.mB) ℂ)
  let QB := PB ⊗ₖ (1 : Matrix (Fin s.mA) (Fin s.mA) ℂ)
  have hQA : IsIsometry QA := hPA.kronecker isIsometry_one
  have hQB : IsIsometry QB := hPB.kronecker isIsometry_one
  let LA := (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ JA
  let LB := (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ JB
  have hLA : (1 - LAᴴ * LA).PosSemidef := posSemidef_identity_kronecker_defect JA hJA
  have hLB : (1 - LBᴴ * LB).PosSemidef := posSemidef_identity_kronecker_defect JB hJB
  have hDA : (1 - P.decAᴴᴴ * P.decAᴴ).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      P.decA_isometry.posSemidef_one_sub_mul_adjoint
  have hDB : (1 - P.decBᴴᴴ * P.decBᴴ).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      P.decB_isometry.posSemidef_one_sub_mul_adjoint
  let CA := QA * P.decAᴴ * LA
  let CB := QB * P.decBᴴ * LB
  have hCA : (1 - CAᴴ * CA).PosSemidef :=
    posSemidef_gram_defect_mul (QA * P.decAᴴ) LA
      (posSemidef_gram_defect_mul QA P.decAᴴ hQA.posSemidef_gram_defect hDA) hLA
  have hCB : (1 - CBᴴ * CB).PosSemidef :=
    posSemidef_gram_defect_mul (QB * P.decBᴴ) LB
      (posSemidef_gram_defect_mul QB P.decBᴴ hQB.posSemidef_gram_defect hDB) hLB
  obtain ⟨TA, hTA, htopA⟩ := s.completeA CA hCA
  obtain ⟨TB, hTB, htopB⟩ := s.completeB CB hCB
  let VA := (PA ⊗ₖ (1 : Matrix (Fin s.mA) (Fin s.mA) ℂ)) * P.encA
  let VB := (PB ⊗ₖ (1 : Matrix (Fin s.mB) (Fin s.mB) ℂ)) * P.encB
  let x : ReverseBlocks s := (P.resource, g, VA, VB, TA, TB)
  have hx : ReverseBlocks.IsValid x :=
    ⟨P.resource_unit, hg, (hPA.kronecker isIsometry_one).mul P.encA_isometry,
      (hPB.kronecker isIsometry_one).mul P.encB_isometry, hTA, hTB⟩
  refine ⟨x, hx, ?_⟩
  let EA := s.rowEmbeddingA * QA
  let EB := s.rowEmbeddingB * QB
  have hea : EAᴴ * TA = P.decAᴴ * LA := by
    change (s.rowEmbeddingA * QA)ᴴ * TA = _
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, htopA]
    change QAᴴ * (QA * P.decAᴴ * LA) = _
    rw [Matrix.mul_assoc QA P.decAᴴ LA, ← Matrix.mul_assoc QAᴴ QA,
      hQA.conjTranspose_mul_self, Matrix.one_mul]
  have heb : EBᴴ * TB = P.decBᴴ * LB := by
    change (s.rowEmbeddingB * QB)ᴴ * TB = _
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, htopB]
    change QBᴴ * (QB * P.decBᴴ * LB) = _
    rw [Matrix.mul_assoc QB P.decBᴴ LB, ← Matrix.mul_assoc QBᴴ QB,
      hQB.conjTranspose_mul_self, Matrix.one_mul]
  have hforward : ReverseBlocks.forward x = (EA ⊗ₖ EB) * P.encodedState := by
    change (s.rowEmbeddingA ⊗ₖ s.rowEmbeddingB) *
      NLQCLean.encodedState P.resource VA VB = _
    simp only [VA, VB, encodedState_private_inclusions, EA, EB, QA, QB,
      Matrix.mul_kronecker_mul, Matrix.mul_assoc]
    rfl
  change (ReverseBlocks.reverse x)ᴴ * ReverseBlocks.forward x = _
  rw [hforward]
  exact reverse_crossGram_overlap P.encodedState P.decA P.decB JA JB EA EB TA TB g v
    hea heb hvrep

section PhysicalCoverage

variable {d : ℕ} {ρA ρB κA κB μA μB eA eB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype eA] [Fintype eB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq eA] [DecidableEq eB]

/-- Physical coverage. Every arbitrary-finite-register protocol of budget
K and score at least `1-epsilon` is covered by a valid bounded six-block
witness. No original private or environment dimension appears in its type. -/
theorem PureProtocol.exists_reverse_witness
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) eA eB)
    (hd : 0 < d) {K : ℕ} {ε : ℝ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hU : IsIsometry U) (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hε : ε < 1) (hscore : 1 - ε ≤ scoreU U P.operationalChannel) :
    ∃ s : ReverseShape d K, ∃ x : ReverseBlocks s, ReverseBlocks.IsValid x ∧
      ‖ReverseBlocks.forward x - ReverseBlocks.reverse x * U‖ ≤ (d : ℝ) * Real.sqrt (2 * ε) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨r, kA, kB, eA', eB', hr, hkA, hkB, _, _, Q, hchan⟩ :=
    P.exists_compressed_forward
  let mA := Fintype.card μA
  let mB := Fintype.card μB
  have hrpos : 0 < r := by
    have h := Q.resource_unit.card_pos
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    exact Nat.pos_of_mul_pos_right h
  have hencA : d * r ≤ kA * mA := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Q.encA_isometry.card_le
  have hencB : d * r ≤ kB * mB := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Q.encB_isometry.card_le
  have hma : 0 < mA := Nat.pos_of_mul_pos_left ((Nat.mul_pos hd hrpos).trans_le hencA)
  have hmb : 0 < mB := Nat.pos_of_mul_pos_left ((Nat.mul_pos hd hrpos).trans_le hencB)
  have hfoot : r * mA * mB ≤ K := by
    have h := (hasFootprint_iff K P.resource).mp hK
    simpa only [← hr] using h
  let s : ReverseShape d K := ⟨r, mA, mB, hrpos, hma, hmb, hfoot⟩
  let R := Q.reindex (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
    (Fintype.equivFin μA).symm (Fintype.equivFin μB).symm (Equiv.refl _) (Equiv.refl _)
  have hRchan : P.operationalChannel = R.operationalChannel :=
    hchan.trans (Q.operationalChannel_reindex (Equiv.refl _) (Equiv.refl _)
      (Equiv.refl _) (Equiv.refl _) (Fintype.equivFin μA).symm (Fintype.equivFin μB).symm
      (Equiv.refl _) (Equiv.refl _)).symm
  have hRK : NLQCLean.HasFootprint K R.resource (Fin mA) (Fin mB) := by
    refine ⟨r, mA, mB, hfoot, ?_, ?_, ?_⟩
    · simpa only [Fintype.card_fin] using schmidtRank_le_card_left R.resource
    · simp
    · simp
  obtain ⟨v, hv, hvrank, hclose⟩ := R.exists_rank_bounded_approx_frozen U hU hRK hε
    (hRchan ▸ hscore)
  obtain ⟨x, hx, hcross⟩ := R.exists_reverse_blocks_of_frozen s hkA hkB v hv hvrank
  refine ⟨s, x, hx, ?_⟩
  have hdist := norm_sub_eq_of_crossGram_eq (ReverseBlocks.forward x) (ReverseBlocks.reverse x)
    R.globalIsometry (insertResource (Fin d) (Fin d) v) U
    hx.isIsometry_forward hx.isIsometry_reverse R.isIsometry_globalIsometry
    (isIsometry_insertResource v hv) hcross
  rw [← hdist] at hclose
  have hD : (Fintype.card (Fin d × Fin d) : ℝ) = (d : ℝ) ^ 2 := by
    simp [pow_two]
  rw [hD, Real.sqrt_sq (Nat.cast_nonneg d)] at hclose
  have h := (div_le_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mp hclose
  simpa only [mul_comm] using h

/-- Physical coverage with the cross-Gram and both leakage bounds included. -/
theorem PureProtocol.exists_reverse_witness_approximation
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) eA eB)
    (hd : 0 < d) {K : ℕ} {ε : ℝ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hU : IsIsometry U) (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hscore : 1 - ε ≤ scoreU U P.operationalChannel) :
    ∃ s : ReverseShape d K, ∃ x : ReverseBlocks s, ReverseBlocks.IsValid x ∧
      ‖ReverseBlocks.forward x - ReverseBlocks.reverse x * U‖ ≤ (d : ℝ) * Real.sqrt (2 * ε) ∧
      ‖ReverseBlocks.overlap x - U‖ ≤ (d : ℝ) * Real.sqrt (2 * ε) ∧
      ‖ReverseBlocks.forward x - ReverseBlocks.reverse x * ReverseBlocks.overlap x‖ ^ 2 =
        (d : ℝ) ^ 2 - ‖ReverseBlocks.overlap x‖ ^ 2 ∧
      ‖ReverseBlocks.reverse x - ReverseBlocks.forward x * (ReverseBlocks.overlap x)ᴴ‖ ^ 2 =
        (d : ℝ) ^ 2 - ‖ReverseBlocks.overlap x‖ ^ 2 ∧
      (d : ℝ) ^ 2 - ‖ReverseBlocks.overlap x‖ ^ 2 ≤ (d : ℝ) ^ 2 * (2 * ε) := by
  obtain ⟨s, x, hx, hclose⟩ := P.exists_reverse_witness hd U hU hK hε hscore
  refine ⟨s, x, hx, hclose, ?_⟩
  have h := hx.approximation U (mul_nonneg (Nat.cast_nonneg d) (Real.sqrt_nonneg _)) hclose
  simpa only [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε0)] using h

end PhysicalCoverage

/-- Exact real coordinate count of the six raw complex block spaces. -/
theorem ReverseBlocks.finrank_real {d K : ℕ} (s : ReverseShape d K) :
    Module.finrank ℝ (ReverseBlocks s) =
      2 * s.r ^ 2 + 2 * K ^ 2 + 2 * d ^ 2 * (s.r * s.mA) ^ 2 +
        2 * d ^ 2 * (s.r * s.mB) ^ 2 + 8 * d ^ 2 * K ^ 2 := by
  rw [finrank_real_of_complex]
  simp only [ReverseBlocks, Module.finrank_prod, Module.finrank_pi, Module.finrank_matrix,
    Module.finrank_self, Fintype.card_prod, Fintype.card_fin]
  ring

/-- Raw dimension bound with an explicit universal constant.
Neither discarded environments nor original private dimensions occur. -/
theorem ReverseBlocks.finrank_real_le {d K : ℕ} (s : ReverseShape d K) (hd : 0 < d) :
    Module.finrank ℝ (ReverseBlocks s) ≤ 16 * d ^ 2 * K ^ 2 := by
  have hA : s.r * s.mA ≤ K :=
    (Nat.le_mul_of_pos_right _ s.messageB_pos).trans s.footprint
  have hB : s.r * s.mB ≤ K := by
    have h := (Nat.le_mul_of_pos_right (s.r * s.mB) s.messageA_pos)
    exact h.trans (by simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using s.footprint)
  have hr : s.r ≤ K := (Nat.le_mul_of_pos_right _ s.messageA_pos).trans hA
  have hr2 : s.r ^ 2 ≤ K ^ 2 := by gcongr
  have ha2 : d ^ 2 * (s.r * s.mA) ^ 2 ≤ d ^ 2 * K ^ 2 := by gcongr
  have hb2 : d ^ 2 * (s.r * s.mB) ^ 2 ≤ d ^ 2 * K ^ 2 := by gcongr
  have hdK : K ^ 2 ≤ d ^ 2 * K ^ 2 := Nat.le_mul_of_pos_left _ (pow_pos hd 2)
  rw [ReverseBlocks.finrank_real]
  nlinarith

end NLQCLean

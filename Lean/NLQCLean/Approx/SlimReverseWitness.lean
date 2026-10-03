import NLQCLean.Approx.ReverseWitness
import NLQCLean.Approx.PolynomialWitnessCoverage
import NLQCLean.Approx.SwapNeighborhoodFreezing
import NLQCLean.Bounds.SwapNeighborhoodMessages

/-!
# Slim six-block reverse witnesses near SWAP

A slim shape is an ordinary reverse shape `(r, m_A, m_B)`
with `r m_A m_B ≤ K` whose two complete messages obey the floors `d² ≤ 2 m²`. The frozen
environment block has support `s = frozenSupport d K`, not `K`; each completed reverse
isometry has `d(K+s)` rows and `ds` columns, with row embeddings fixed by the shape.

* `PureProtocol.exists_slim_reverse_witness`: every pure protocol on arbitrary finite registers
  with footprint `K`, target `U ∈ S_d` and score `≥ 1 − e`, `0 ≤ e ≤ 1/16`, is covered by a
  valid slim six-block witness at Frobenius distance `d √(21 e / 2)`.
* `SlimReverseBlocks.finrank_real` is the exact real dimension of the block space, and
  `SlimReverseBlocks.finrank_real_le` bounds it by `38 K²`.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker MatrixOrder ComplexOrder

/-- Slim shapes: reverse shapes whose complete messages satisfy the message-dimension floors. -/
abbrev SlimReverseShape (d K : ℕ) :=
  {s : ReverseShape d K // d ^ 2 ≤ 2 * s.mA ^ 2 ∧ d ^ 2 ≤ 2 * s.mB ^ 2}

namespace SlimReverseShape

theorem card_le_cube (d K : ℕ) : Fintype.card (SlimReverseShape d K) ≤ K ^ 3 :=
  (Fintype.card_subtype_le _).trans (ReverseShape.card_le_cube d K)

variable {d K : ℕ} (s : SlimReverseShape d K)

theorem sq_le_two_mul_messages : d ^ 2 ≤ 2 * (s.1.mA * s.1.mB) := by
  obtain ⟨hA, hB⟩ := s.2
  apply (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp
  calc (d ^ 2) ^ 2 = d ^ 2 * d ^ 2 := by ring
    _ ≤ (2 * s.1.mA ^ 2) * (2 * s.1.mB ^ 2) := Nat.mul_le_mul hA hB
    _ = (2 * (s.1.mA * s.1.mB)) ^ 2 := by ring

theorem sq_le_two_mul_budget (s : SlimReverseShape d K) : d ^ 2 ≤ 2 * K := by
  have h1 : s.1.mA * s.1.mB ≤ s.1.r * s.1.mA * s.1.mB := by
    rw [Nat.mul_assoc]
    exact Nat.le_mul_of_pos_left _ s.1.resource_pos
  have h2 := s.1.footprint
  have h3 := sq_le_two_mul_messages s
  omega

theorem completion_rowsA :
    Fintype.card (Fin (d * s.1.r * s.1.mA) × Fin s.1.mB) +
      Fintype.card (Fin d × Fin (frozenSupport d K)) ≤ d * (K + frozenSupport d K) := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  have h : d * s.1.r * s.1.mA * s.1.mB ≤ d * K := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left d s.1.footprint
  nlinarith

theorem completion_rowsB :
    Fintype.card (Fin (d * s.1.r * s.1.mB) × Fin s.1.mA) +
      Fintype.card (Fin d × Fin (frozenSupport d K)) ≤ d * (K + frozenSupport d K) := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  have h : d * s.1.r * s.1.mB * s.1.mA ≤ d * K := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_left d s.1.footprint
  nlinarith

/-- Fixed by the shape, before the target or the six blocks are chosen. -/
noncomputable def rowEmbeddingA :
    Matrix (Fin (d * (K + frozenSupport d K))) (Fin (d * s.1.r * s.1.mA) × Fin s.1.mB) ℂ :=
  Classical.choose (exists_uniform_isometric_completion_with_rows
    (Fin (d * s.1.r * s.1.mA) × Fin s.1.mB) (Fin d × Fin (frozenSupport d K))
    (d * (K + frozenSupport d K)) s.completion_rowsA)

noncomputable def rowEmbeddingB :
    Matrix (Fin (d * (K + frozenSupport d K))) (Fin (d * s.1.r * s.1.mB) × Fin s.1.mA) ℂ :=
  Classical.choose (exists_uniform_isometric_completion_with_rows
    (Fin (d * s.1.r * s.1.mB) × Fin s.1.mA) (Fin d × Fin (frozenSupport d K))
    (d * (K + frozenSupport d K)) s.completion_rowsB)

theorem isIsometry_rowEmbeddingA : IsIsometry s.rowEmbeddingA :=
  (Classical.choose_spec (exists_uniform_isometric_completion_with_rows
    (Fin (d * s.1.r * s.1.mA) × Fin s.1.mB) (Fin d × Fin (frozenSupport d K))
    (d * (K + frozenSupport d K)) s.completion_rowsA)).1

theorem isIsometry_rowEmbeddingB : IsIsometry s.rowEmbeddingB :=
  (Classical.choose_spec (exists_uniform_isometric_completion_with_rows
    (Fin (d * s.1.r * s.1.mB) × Fin s.1.mA) (Fin d × Fin (frozenSupport d K))
    (d * (K + frozenSupport d K)) s.completion_rowsB)).1

theorem completeA
    (C : Matrix (Fin (d * s.1.r * s.1.mA) × Fin s.1.mB) (Fin d × Fin (frozenSupport d K)) ℂ)
    (hC : (1 - Cᴴ * C).PosSemidef) :
    ∃ T : Matrix (Fin (d * (K + frozenSupport d K))) (Fin d × Fin (frozenSupport d K)) ℂ,
      IsIsometry T ∧ s.rowEmbeddingAᴴ * T = C :=
  (Classical.choose_spec (exists_uniform_isometric_completion_with_rows
    (Fin (d * s.1.r * s.1.mA) × Fin s.1.mB) (Fin d × Fin (frozenSupport d K))
    (d * (K + frozenSupport d K)) s.completion_rowsA)).2 C hC

theorem completeB
    (C : Matrix (Fin (d * s.1.r * s.1.mB) × Fin s.1.mA) (Fin d × Fin (frozenSupport d K)) ℂ)
    (hC : (1 - Cᴴ * C).PosSemidef) :
    ∃ T : Matrix (Fin (d * (K + frozenSupport d K))) (Fin d × Fin (frozenSupport d K)) ℂ,
      IsIsometry T ∧ s.rowEmbeddingBᴴ * T = C :=
  (Classical.choose_spec (exists_uniform_isometric_completion_with_rows
    (Fin (d * s.1.r * s.1.mB) × Fin s.1.mA) (Fin d × Fin (frozenSupport d K))
    (d * (K + frozenSupport d K)) s.completion_rowsB)).2 C hC

end SlimReverseShape

/-- The six slim blocks: resource, rank-`s` frozen environment, two forward encoders, and two
completed reverse isometries with `d(K+s)` rows and `ds` columns. -/
abbrev SlimReverseBlocks {d K : ℕ} (s : SlimReverseShape d K) :=
  (Fin s.1.r × Fin s.1.r → ℂ) × (Fin (frozenSupport d K) × Fin (frozenSupport d K) → ℂ) ×
    Matrix (Fin (d * s.1.r * s.1.mA) × Fin s.1.mA) (Fin d × Fin s.1.r) ℂ ×
    Matrix (Fin (d * s.1.r * s.1.mB) × Fin s.1.mB) (Fin d × Fin s.1.r) ℂ ×
    Matrix (Fin (d * (K + frozenSupport d K))) (Fin d × Fin (frozenSupport d K)) ℂ ×
    Matrix (Fin (d * (K + frozenSupport d K))) (Fin d × Fin (frozenSupport d K)) ℂ

namespace SlimReverseBlocks

variable {d K : ℕ} {s : SlimReverseShape d K}

def IsValid (x : SlimReverseBlocks s) : Prop :=
  IsUnitVector x.1 ∧ IsUnitVector x.2.1 ∧ IsIsometry x.2.2.1 ∧
    IsIsometry x.2.2.2.1 ∧ IsIsometry x.2.2.2.2.1 ∧ IsIsometry x.2.2.2.2.2

noncomputable def forward (x : SlimReverseBlocks s) :
    Matrix (Fin (d * (K + frozenSupport d K)) × Fin (d * (K + frozenSupport d K)))
      (Fin d × Fin d) ℂ :=
  (s.rowEmbeddingA ⊗ₖ s.rowEmbeddingB) * encodedState x.1 x.2.2.1 x.2.2.2.1

def reverse (x : SlimReverseBlocks s) :
    Matrix (Fin (d * (K + frozenSupport d K)) × Fin (d * (K + frozenSupport d K)))
      (Fin d × Fin d) ℂ :=
  (x.2.2.2.2.1 ⊗ₖ x.2.2.2.2.2) * insertResource (Fin d) (Fin d) x.2.1

noncomputable def overlap (x : SlimReverseBlocks s) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (reverse x)ᴴ * forward x

theorem IsValid.isIsometry_forward {x : SlimReverseBlocks s} (hx : IsValid x) :
    IsIsometry (forward x) :=
  (s.isIsometry_rowEmbeddingA.kronecker s.isIsometry_rowEmbeddingB).mul
    (isIsometry_encodedState hx.1 hx.2.2.1 hx.2.2.2.1)

theorem IsValid.isIsometry_reverse {x : SlimReverseBlocks s} (hx : IsValid x) :
    IsIsometry (reverse x) :=
  (hx.2.2.2.2.1.kronecker hx.2.2.2.2.2).mul (isIsometry_insertResource _ hx.2.1)

/-- The exact leakage identities for every valid slim witness. -/
theorem IsValid.approximation {x : SlimReverseBlocks s} (hx : IsValid x)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    {η : ℝ} (hη : 0 ≤ η) (hclose : ‖forward x - reverse x * U‖ ≤ η) :
    ‖overlap x - U‖ ≤ η ∧
      ‖forward x - reverse x * overlap x‖ ^ 2 = (d : ℝ) ^ 2 - ‖overlap x‖ ^ 2 ∧
      ‖reverse x - forward x * (overlap x)ᴴ‖ ^ 2 = (d : ℝ) ^ 2 - ‖overlap x‖ ^ 2 ∧
      (d : ℝ) ^ 2 - ‖overlap x‖ ^ 2 ≤ η ^ 2 := by
  have h := crossGram_approximation (forward x) (reverse x) U
    hx.isIsometry_forward hx.isIsometry_reverse hη hclose
  simpa only [overlap, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two] using h

/-- Exact real coordinate count of the six slim block spaces. -/
theorem finrank_real (s : SlimReverseShape d K) :
    Module.finrank ℝ (SlimReverseBlocks s) =
      2 * s.1.r ^ 2 + 2 * frozenSupport d K ^ 2 + 2 * d ^ 2 * (s.1.r * s.1.mA) ^ 2 +
        2 * d ^ 2 * (s.1.r * s.1.mB) ^ 2 +
        4 * d ^ 2 * ((K + frozenSupport d K) * frozenSupport d K) := by
  rw [finrank_real_of_complex]
  simp only [SlimReverseBlocks, Module.finrank_prod, Module.finrank_pi, Module.finrank_matrix,
    Module.finrank_self, Fintype.card_prod, Fintype.card_fin]
  ring

/-- Raw dimension bound: the slim block space has real dimension `≤ 38 K²`. -/
theorem finrank_real_le (s : SlimReverseShape d K) (hd : 2 ≤ d) :
    Module.finrank ℝ (SlimReverseBlocks s) ≤ 38 * K ^ 2 := by
  obtain ⟨hA, hB⟩ := s.2
  have hK2 := SlimReverseShape.sq_le_two_mul_budget s
  have hdfs := sq_mul_frozenSupport_le (by omega : 0 < d) hK2
  have hf := s.1.footprint
  have hd4 : 4 ≤ d ^ 2 := by nlinarith
  have hK : 2 ≤ K := by omega
  have hmA : 2 ≤ s.1.mA := by
    by_contra h
    have : s.1.mA ^ 2 ≤ 1 := by
      have : s.1.mA ≤ 1 := by omega
      nlinarith
    omega
  have hmB : 2 ≤ s.1.mB := by
    by_contra h
    have : s.1.mB ^ 2 ≤ 1 := by
      have : s.1.mB ≤ 1 := by omega
      nlinarith
    omega
  have hr4 : 4 * s.1.r ≤ K := by
    have : s.1.r * 2 * 2 ≤ s.1.r * s.1.mA * s.1.mB :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hmA) hmB
    omega
  have hq2 : 2 ≤ flatSupportCount d := by
    have := two_mul_flatSupportCount_le d
    have := sq_le_two_mul_flatSupportCount d
    omega
  have hf2 : 2 * frozenSupport d K ≤ K + 1 := by
    have hb := (flatSupportCount_mul_frozenSupport_bounds (by omega : 0 < d) K).2
    rcases Nat.eq_zero_or_pos (frozenSupport d K) with h0 | h0
    · omega
    · obtain ⟨g, hg⟩ : ∃ g, frozenSupport d K = g + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h0).symm⟩
      rw [hg] at hb ⊢
      have hmul : 2 * g ≤ flatSupportCount d * g := Nat.mul_le_mul_right g hq2
      have : flatSupportCount d * (g + 1) = flatSupportCount d * g + flatSupportCount d := by ring
      omega
  have hAenc : d ^ 2 * (s.1.r * s.1.mA) ^ 2 ≤ 2 * K ^ 2 := by
    calc d ^ 2 * (s.1.r * s.1.mA) ^ 2 ≤ (2 * s.1.mB ^ 2) * (s.1.r * s.1.mA) ^ 2 :=
          Nat.mul_le_mul_right _ hB
      _ = 2 * (s.1.r * s.1.mA * s.1.mB) ^ 2 := by ring
      _ ≤ 2 * K ^ 2 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hf 2)
  have hBenc : d ^ 2 * (s.1.r * s.1.mB) ^ 2 ≤ 2 * K ^ 2 := by
    calc d ^ 2 * (s.1.r * s.1.mB) ^ 2 ≤ (2 * s.1.mA ^ 2) * (s.1.r * s.1.mB) ^ 2 :=
          Nat.mul_le_mul_right _ hA
      _ = 2 * (s.1.r * s.1.mA * s.1.mB) ^ 2 := by ring
      _ ≤ 2 * K ^ 2 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hf 2)
  have hcomp : 4 * (d ^ 2 * ((K + frozenSupport d K) * frozenSupport d K)) ≤ 28 * K ^ 2 := by
    have h7 : 4 * (K + frozenSupport d K) ≤ 7 * K := by omega
    calc 4 * (d ^ 2 * ((K + frozenSupport d K) * frozenSupport d K)) =
        (4 * (K + frozenSupport d K)) * (d ^ 2 * frozenSupport d K) := by ring
      _ ≤ (7 * K) * (4 * K) := Nat.mul_le_mul h7 hdfs
      _ = 28 * K ^ 2 := by ring
  have hr2 : 16 * s.1.r ^ 2 ≤ K ^ 2 := by
    have := Nat.pow_le_pow_left hr4 2
    nlinarith
  have hs2 : 16 * frozenSupport d K ^ 2 ≤ 9 * K ^ 2 := by
    have := Nat.pow_le_pow_left hf2 2
    nlinarith
  rw [finrank_real]
  nlinarith

end SlimReverseBlocks

/-- W:compress--W:overlap for slim shapes: the rank-`s` frozen environment is represented
exactly on `Fin s`, and completion absorbs the backward contractions. -/
theorem PureProtocol.exists_slim_blocks_of_frozen
    {d K kA kB : ℕ} (s : SlimReverseShape d K) {eA eB : Type*}
    [Fintype eA] [Fintype eB] [DecidableEq eA] [DecidableEq eB]
    (P : PureProtocol (Fin d) (Fin d) (Fin s.1.r) (Fin s.1.r) (Fin kA) (Fin kB)
      (Fin s.1.mA) (Fin s.1.mB) (Fin d) (Fin d) eA eB)
    (hkA : kA ≤ d * s.1.r * s.1.mA) (hkB : kB ≤ d * s.1.r * s.1.mB)
    (v : eA × eB → ℂ) (hv : IsUnitVector v) (hvrank : schmidtRank v ≤ frozenSupport d K) :
    ∃ x : SlimReverseBlocks s, SlimReverseBlocks.IsValid x ∧
      SlimReverseBlocks.overlap x = (insertResource (Fin d) (Fin d) v)ᴴ * P.globalIsometry := by
  obtain ⟨PA, hPA⟩ := exists_isometry_of_card_le
    (m := Fin kA) (n := Fin (d * s.1.r * s.1.mA)) (by simpa using hkA)
  obtain ⟨PB, hPB⟩ := exists_isometry_of_card_le
    (m := Fin kB) (n := Fin (d * s.1.r * s.1.mB)) (by simpa using hkB)
  obtain ⟨JA, JB, g, hg, hJA, hJB, hvrep⟩ := exists_padded_resource_support v hv hvrank
  let QA := PA ⊗ₖ (1 : Matrix (Fin s.1.mB) (Fin s.1.mB) ℂ)
  let QB := PB ⊗ₖ (1 : Matrix (Fin s.1.mA) (Fin s.1.mA) ℂ)
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
  let VA := (PA ⊗ₖ (1 : Matrix (Fin s.1.mA) (Fin s.1.mA) ℂ)) * P.encA
  let VB := (PB ⊗ₖ (1 : Matrix (Fin s.1.mB) (Fin s.1.mB) ℂ)) * P.encB
  let x : SlimReverseBlocks s := (P.resource, g, VA, VB, TA, TB)
  have hx : SlimReverseBlocks.IsValid x :=
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
  have hforward : SlimReverseBlocks.forward x = (EA ⊗ₖ EB) * P.encodedState := by
    change (s.rowEmbeddingA ⊗ₖ s.rowEmbeddingB) *
      NLQCLean.encodedState P.resource VA VB = _
    simp only [VA, VB, encodedState_private_inclusions, EA, EB, QA, QB,
      Matrix.mul_kronecker_mul, Matrix.mul_assoc]
    rfl
  change (SlimReverseBlocks.reverse x)ᴴ * SlimReverseBlocks.forward x = _
  rw [hforward]
  exact reverse_crossGram_overlap P.encodedState P.decA P.decB JA JB EA EB TA TB g v
    hea heb hvrep

section PhysicalCoverage

variable {d : ℕ} {ρA ρB κA κB μA μB eA eB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype eA] [Fintype eB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq eA] [DecidableEq eB]

/-- Physical coverage near SWAP: a valid slim witness at distance `d √(21 e / 2)`. -/
theorem PureProtocol.exists_slim_reverse_witness
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) eA eB) (hd : 2 ≤ d)
    {U : Matrix.unitaryGroup (Fin d × Fin d) ℂ} (hU : U ∈ swapNeighborhood d)
    {K : ℕ} (hK : NLQCLean.HasFootprint K P.resource μA μB) {e : ℝ} (he0 : 0 ≤ e)
    (he : e ≤ 1 / 16)
    (hscore : 1 - e ≤ scoreU (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) P.operationalChannel) :
    ∃ s : SlimReverseShape d K, ∃ x : SlimReverseBlocks s, SlimReverseBlocks.IsValid x ∧
      ‖SlimReverseBlocks.forward x -
          SlimReverseBlocks.reverse x * (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)‖ ≤
        (d : ℝ) * Real.sqrt (21 / 2 * e) := by
  have hd0 : 0 < d := by omega
  let : NeZero d := ⟨hd0.ne'⟩
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
  have hma : 0 < mA := Nat.pos_of_mul_pos_left ((Nat.mul_pos hd0 hrpos).trans_le hencA)
  have hmb : 0 < mB := Nat.pos_of_mul_pos_left ((Nat.mul_pos hd0 hrpos).trans_le hencB)
  have hfoot : r * mA * mB ≤ K := by
    have h := (hasFootprint_iff K P.resource).mp hK
    simpa only [← hr] using h
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
  have hRscore : 1 - e ≤ scoreU (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
      R.operationalChannel := hRchan ▸ hscore
  obtain ⟨hfA, hfB⟩ := R.sq_le_two_mul_message_sq_of_mem_swapNeighborhood hd0 hU he hRscore
  simp only [Fintype.card_fin] at hfA hfB
  have hfA' : d ^ 2 ≤ 2 * mA ^ 2 := by exact_mod_cast hfA
  have hfB' : d ^ 2 ≤ 2 * mB ^ 2 := by exact_mod_cast hfB
  let s : SlimReverseShape d K := ⟨⟨r, mA, mB, hrpos, hma, hmb, hfoot⟩, hfA', hfB'⟩
  obtain ⟨v, hv, hvrank, hclose⟩ :=
    R.exists_small_support_approx_frozen hd hU hRK he0 he hRscore
  obtain ⟨x, hx, hcross⟩ := R.exists_slim_blocks_of_frozen s hkA hkB v hv hvrank
  refine ⟨s, x, hx, ?_⟩
  have hdist := norm_sub_eq_of_crossGram_eq (SlimReverseBlocks.forward x)
    (SlimReverseBlocks.reverse x) R.globalIsometry (insertResource (Fin d) (Fin d) v)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    hx.isIsometry_forward hx.isIsometry_reverse R.isIsometry_globalIsometry
    (isIsometry_insertResource v hv) hcross
  rw [← hdist] at hclose
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have h := (div_le_iff₀ hdR).mp hclose
  simpa only [mul_comm] using h

end PhysicalCoverage

end NLQCLean

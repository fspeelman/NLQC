import NLQCLean.Approx.PVMReverseWitness

/-!
# Physical realization of compressed PVM reverse witnesses

Exact flagged Schmidt supports from a frozen PVM dilation are
pulled back through the physical decoders.  Their contractions are completed
inside the fixed row spaces determined by the charged architecture and the
positive per-label rank allocation.
-/

namespace NLQCLean

open Matrix
open scoped Kronecker MatrixOrder ComplexOrder

/-- A compressed physical protocol and a normalized frozen PVM environment
family determine one valid reverse witness in the family indexed by the
family's exact positive Schmidt-rank allocation.  Its overlap is exactly the
physical cross-Gram matrix. -/
theorem PureProtocol.exists_pvm_reverse_blocks_of_frozen
    {d K kA kB : ℕ} (arch : ReverseShape d K) {eA eB : Type*}
    [Fintype eA] [Fintype eB] [DecidableEq eA] [DecidableEq eB]
    (P : PureProtocol (Fin d) (Fin d) (Fin arch.r) (Fin arch.r) (Fin kA) (Fin kB)
      (Fin arch.mA) (Fin arch.mB) (Fin d × Fin d) (Fin d × Fin d) eA eB)
    (hkA : kA ≤ d * arch.r * arch.mA) (hkB : kB ≤ d * arch.r * arch.mB)
    (u : (Fin d × Fin d) → eA × eB → ℂ)
    (hu : ∀ i, IsUnitVector (u i))
    (hurank : ∑ i, schmidtRank (u i) ≤ K + Fintype.card (Fin d × Fin d)) :
    ∃ allocation : PositiveRankAllocation (Fin d × Fin d) K,
      (∀ i, allocation.rank i = schmidtRank (u i)) ∧
      ∃ x : PVMReverseBlocks (arch, allocation), PVMReverseBlocks.IsValid x ∧
        PVMReverseBlocks.overlap x = (flagIsometry u)ᴴ * P.globalIsometry := by
  classical
  let allocation : PositiveRankAllocation (Fin d × Fin d) K :=
    ⟨fun i ↦ schmidtRank (u i), fun i ↦ (hu i).schmidtRank_pos, hurank⟩
  let s : PVMReverseShape d K := (arch, allocation)
  obtain ⟨PA, hPA⟩ := exists_isometry_of_card_le
    (m := Fin kA) (n := Fin (d * arch.r * arch.mA)) (by simpa using hkA)
  obtain ⟨PB, hPB⟩ := exists_isometry_of_card_le
    (m := Fin kB) (n := Fin (d * arch.r * arch.mB)) (by simpa using hkB)
  obtain ⟨JA, JB, g, hJA, hJB, hg, hfac, hLAiso, hLBiso, _, hflag⟩ :=
    exists_flagged_support_factorization u hu
  let QA := PA ⊗ₖ (1 : Matrix (Fin arch.mB) (Fin arch.mB) ℂ)
  let QB := PB ⊗ₖ (1 : Matrix (Fin arch.mA) (Fin arch.mA) ℂ)
  have hQA : IsIsometry QA := hPA.kronecker isIsometry_one
  have hQB : IsIsometry QB := hPB.kronecker isIsometry_one
  let LA := localFlagInclusion JA
  let LB := localFlagInclusion JB
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
      (posSemidef_gram_defect_mul QA P.decAᴴ hQA.posSemidef_gram_defect hDA)
      hLAiso.posSemidef_gram_defect
  have hCB : (1 - CBᴴ * CB).PosSemidef :=
    posSemidef_gram_defect_mul (QB * P.decBᴴ) LB
      (posSemidef_gram_defect_mul QB P.decBᴴ hQB.posSemidef_gram_defect hDB)
      hLBiso.posSemidef_gram_defect
  obtain ⟨TA, hTA, htopA⟩ := s.completeA CA hCA
  obtain ⟨TB, hTB, htopB⟩ := s.completeB CB hCB
  let VA := (PA ⊗ₖ (1 : Matrix (Fin arch.mA) (Fin arch.mA) ℂ)) * P.encA
  let VB := (PB ⊗ₖ (1 : Matrix (Fin arch.mB) (Fin arch.mB) ℂ)) * P.encB
  let x : PVMReverseBlocks s := (P.resource, g, VA, VB, TA, TB)
  have hx : PVMReverseBlocks.IsValid x :=
    ⟨P.resource_unit, hg, (hPA.kronecker isIsometry_one).mul P.encA_isometry,
      (hPB.kronecker isIsometry_one).mul P.encB_isometry, hTA, hTB⟩
  refine ⟨allocation, fun i => rfl, x, hx, ?_⟩
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
  have hforward : PVMReverseBlocks.forward x = (EA ⊗ₖ EB) * P.encodedState := by
    change (s.rowEmbeddingA ⊗ₖ s.rowEmbeddingB) *
      NLQCLean.encodedState P.resource VA VB = _
    simp only [VA, VB, encodedState_private_inclusions, EA, EB, QA, QB,
      Matrix.mul_kronecker_mul, Matrix.mul_assoc]
    rfl
  change (PVMReverseBlocks.reverse x)ᴴ * PVMReverseBlocks.forward x = _
  rw [hforward]
  exact pvm_reverse_crossGram_overlap P.encodedState P.decA P.decB LA LB EA EB TA TB
    (compressedFlag g) (flagIsometry u) hea heb hflag

end NLQCLean

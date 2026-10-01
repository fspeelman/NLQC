import NLQCLean.LinearAlgebra.SupportFactorization
import NLQCLean.Models.Resource
import NLQCLean.Models.ForwardReindex

/-!
# Exact finite compression of forward protocols

Resource supports use the actual coefficient-matrix rank. The private and
environment supports are coefficient spans of the forward maps. All
factorizations are exact and preserve isometries; no padded extensions or
approximation hypotheses enter.
-/

namespace NLQCLean

open Matrix
open scoped Kronecker

/-- Pure-resource support factorization on exactly `r × r` coordinates,
where `r` is the existing rank-based `schmidtRank`. Bob's support is obtained
from coefficient rows, not from their complex conjugates. -/
theorem exists_resource_support_factorization {ρA ρB : Type*}
    [Fintype ρA] [Fintype ρB] [DecidableEq ρA] [DecidableEq ρB]
    (η : ρA × ρB → ℂ) (hη : IsUnitVector η) :
    ∃ JA : Matrix ρA (Fin (schmidtRank η)) ℂ,
      ∃ JB : Matrix ρB (Fin (schmidtRank η)) ℂ,
        ∃ η' : Fin (schmidtRank η) × Fin (schmidtRank η) → ℂ,
          IsIsometry JA ∧ IsIsometry JB ∧ IsUnitVector η' ∧
            η = (JA ⊗ₖ JB) *ᵥ η' := by
  unfold schmidtRank
  obtain ⟨JA, JB, B, hJA, hJB, hB⟩ :=
    exists_isometry_two_sided_factorization (resourceMatrix η)
  let η' : Fin (resourceMatrix η).rank × Fin (resourceMatrix η).rank → ℂ :=
    fun p => B p.1 p.2
  have hηeq : η = (JA ⊗ₖ JB) *ᵥ η' := by
    exact (funext fun p : ρA × ρB => congrArg (fun M : Matrix ρA ρB ℂ => M p.1 p.2) hB).trans
      (kronecker_mulVec_coefficients JA JB B).symm
  refine ⟨JA, JB, η', hJA, hJB, ?_, hηeq⟩
  exact ((hJA.kronecker hJB).isUnitVector_mulVec_iff η').mp (hηeq ▸ hη)

section Wiring

variable {ιA ιB ιA' ιB' ρA ρB ρA' ρB' κA κB κA' κB' μA μB εA εB εA' εB' : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ιA'] [Fintype ιB']
variable [Fintype ρA] [Fintype ρB] [Fintype ρA'] [Fintype ρB']
variable [Fintype κA] [Fintype κB] [Fintype κA'] [Fintype κB']
variable [Fintype μA] [Fintype μB]
variable [Fintype εA] [Fintype εB] [Fintype εA'] [Fintype εB']
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ιA'] [DecidableEq ιB']
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq ρA'] [DecidableEq ρB']
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq κA'] [DecidableEq κB']
variable [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq εA] [DecidableEq εB] [DecidableEq εA'] [DecidableEq εB']

omit [Fintype ρA] [Fintype ρB] [DecidableEq ρA] [DecidableEq ρB] [DecidableEq ρA'] [DecidableEq ρB'] in
/-- Resource inclusions can be absorbed into the encoder inputs. -/
theorem insertResource_tensor_mulVec (JA : Matrix ρA ρA' ℂ) (JB : Matrix ρB ρB' ℂ)
    (η : ρA' × ρB' → ℂ) :
    insertResource ιA ιB ((JA ⊗ₖ JB) *ᵥ η) =
      (((1 : Matrix ιA ιA ℂ) ⊗ₖ JA) ⊗ₖ ((1 : Matrix ιB ιB ℂ) ⊗ₖ JB)) *
        insertResource ιA ιB η := by
  ext p q
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, insertResource_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply,
    Finset.mul_sum]

omit [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB] [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB] in
omit [DecidableEq ρA] [DecidableEq ρB] [DecidableEq ρA'] [DecidableEq ρB'] in
/-- Exact resource compression leaves the global forward dilation unchanged. -/
theorem globalIsometry_resource_inclusions
    (JA : Matrix ρA ρA' ℂ) (JB : Matrix ρB ρB' ℂ) (η : ρA' × ρB' → ℂ)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ) :
    globalIsometry ((JA ⊗ₖ JB) *ᵥ η) VA VB DA DB =
      globalIsometry η (VA * ((1 : Matrix ιA ιA ℂ) ⊗ₖ JA))
        (VB * ((1 : Matrix ιB ιB ℂ) ⊗ₖ JB)) DA DB := by
  simp only [globalIsometry, encodedState, insertResource_tensor_mulVec,
    Matrix.mul_kronecker_mul, Matrix.mul_assoc]

/-- The canonical exchange commutes with inclusions of the retained spaces. -/
theorem exchangeMatrix_private_inclusions
    (KA : Matrix κA κA' ℂ) (KB : Matrix κB κB' ℂ) :
    exchangeMatrix κA μA κB μB *
        ((KA ⊗ₖ (1 : Matrix μA μA ℂ)) ⊗ₖ (KB ⊗ₖ (1 : Matrix μB μB ℂ))) =
      ((KA ⊗ₖ (1 : Matrix μB μB ℂ)) ⊗ₖ (KB ⊗ₖ (1 : Matrix μA μA ℂ))) *
        exchangeMatrix κA' μA κB' μB := by
  rw [exchangeMatrix_mul, exchangeMatrix, Matrix.mul_submatrix_one]
  ext p q
  change KA p.1.1 q.1.1 * (1 : Matrix μA μA ℂ) p.2.2 q.1.2 *
      (KB p.2.1 q.2.1 * (1 : Matrix μB μB ℂ) p.1.2 q.2.2) =
    KA p.1.1 q.1.1 * (1 : Matrix μB μB ℂ) p.1.2 q.2.2 *
      (KB p.2.1 q.2.1 * (1 : Matrix μA μA ℂ) p.2.2 q.1.2)
  ring

omit [DecidableEq ρA] [DecidableEq ρB] in
/-- Private-space inclusions pass through the exchange into the decoder inputs. -/
theorem encodedState_private_inclusions
    (KA : Matrix κA κA' ℂ) (KB : Matrix κB κB' ℂ) (η : ρA × ρB → ℂ)
    (VA : Matrix (κA' × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB' × μB) (ιB × ρB) ℂ) :
    encodedState η ((KA ⊗ₖ (1 : Matrix μA μA ℂ)) * VA)
        ((KB ⊗ₖ (1 : Matrix μB μB ℂ)) * VB) =
      ((KA ⊗ₖ (1 : Matrix μB μB ℂ)) ⊗ₖ (KB ⊗ₖ (1 : Matrix μA μA ℂ))) *
        encodedState η VA VB := by
  simp only [encodedState, Matrix.mul_kronecker_mul]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, exchangeMatrix_private_inclusions]
  simp only [Matrix.mul_assoc]

omit [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB] [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB] in
omit [DecidableEq ρA] [DecidableEq ρB] in
/-- Exact private compression preserves the forward dilation after restriction
of the decoders to the reachable post-exchange inputs. -/
theorem globalIsometry_private_inclusions
    (KA : Matrix κA κA' ℂ) (KB : Matrix κB κB' ℂ) (η : ρA × ρB → ℂ)
    (VA : Matrix (κA' × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB' × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ) :
    globalIsometry η ((KA ⊗ₖ (1 : Matrix μA μA ℂ)) * VA)
        ((KB ⊗ₖ (1 : Matrix μB μB ℂ)) * VB) DA DB =
      globalIsometry η VA VB (DA * (KA ⊗ₖ (1 : Matrix μB μB ℂ)))
        (DB * (KB ⊗ₖ (1 : Matrix μA μA ℂ))) := by
  simp only [globalIsometry, encodedState_private_inclusions, decoder,
    Matrix.mul_kronecker_mul, Matrix.mul_assoc]

omit [Fintype ιA] [Fintype ιB] [Fintype εA] [Fintype εB] [DecidableEq ιA] [DecidableEq ιB] [DecidableEq εA] [DecidableEq εB] [DecidableEq εA'] [DecidableEq εB'] in
/-- Environment embeddings become a single environment embedding after output
regrouping, with the logical output unchanged. -/
theorem regroup_environment_inclusions
    (EA : Matrix εA εA' ℂ) (EB : Matrix εB εB' ℂ)
    (F : Matrix ((ιA' × εA') × (ιB' × εB')) (ιA × ιB) ℂ) :
    ((((1 : Matrix ιA' ιA' ℂ) ⊗ₖ EA) ⊗ₖ ((1 : Matrix ιB' ιB' ℂ) ⊗ₖ EB)) * F).submatrix
        (outputRegroup ιA' ιB' εA εB) id =
      ((1 : Matrix (ιA' × ιB') (ιA' × ιB') ℂ) ⊗ₖ (EA ⊗ₖ EB)) *
        F.submatrix (outputRegroup ιA' ιB' εA' εB') id := by
  rw [Matrix.submatrix_mul _ _ _ (outputRegroup ιA' ιB' εA' εB') id
    (outputRegroup ιA' ιB' εA' εB').bijective]
  congr 1
  ext p q
  by_cases hA : p.1.1 = q.1.1 <;> by_cases hB : p.1.2 = q.1.2 <;>
    simp [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, outputRegroup_apply,
      Matrix.one_apply, Prod.ext_iff, hA, hB]

end Wiring

/-- Isometric enlargement of a discarded environment leaves the partial trace
unchanged, for arbitrary input matrices. -/
theorem ptraceB_isometry_conjugation {ι ε ε' : Type*}
    [Fintype ι] [Fintype ε] [Fintype ε']
    [DecidableEq ι] [DecidableEq ε] [DecidableEq ε']
    (J : Matrix ε ε' ℂ) (hJ : IsIsometry J)
    (M : Matrix (ι × ε') (ι × ε') ℂ) :
    ptraceB ι ε (((1 : Matrix ι ι ℂ) ⊗ₖ J) * M * ((1 : Matrix ι ι ℂ) ⊗ₖ J)ᴴ) =
      ptraceB ι ε' M := by
  ext i j
  have hblock :
      (((1 : Matrix ι ι ℂ) ⊗ₖ J) * M * ((1 : Matrix ι ι ℂ) ⊗ₖ J)ᴴ).submatrix
          (fun e => (i, e)) (fun e => (j, e)) =
        J * M.submatrix (fun e => (i, e)) (fun e => (j, e)) * Jᴴ := by
    ext e f
    simp [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply,
      Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply, apply_ite]
  change ((((1 : Matrix ι ι ℂ) ⊗ₖ J) * M * ((1 : Matrix ι ι ℂ) ⊗ₖ J)ᴴ).submatrix
      (fun e => (i, e)) (fun e => (j, e))).trace =
    (M.submatrix (fun e => (i, e)) (fun e => (j, e))).trace
  rw [hblock, Matrix.trace_mul_cycle, hJ.conjTranspose_mul_self, Matrix.one_mul]

/-- The operational channel is invariant under an isometric inclusion in the
discarded environment. No isometry hypothesis on the input dilation is needed. -/
theorem channelOf_environment_inclusion {ι κ ε ε' : Type*}
    [Fintype ι] [Fintype κ] [Fintype ε] [Fintype ε']
    [DecidableEq ι] [DecidableEq κ] [DecidableEq ε] [DecidableEq ε']
    (J : Matrix ε ε' ℂ) (hJ : IsIsometry J) (F : Matrix (κ × ε') ι ℂ) :
    channelOf (((1 : Matrix κ κ ℂ) ⊗ₖ J) * F) = channelOf F := by
  ext M i j
  simp only [channelOf_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have h := ptraceB_isometry_conjugation J hJ (F * M * Fᴴ)
  simpa only [Matrix.mul_assoc] using congrArg (fun N : Matrix κ κ ℂ => N i j) h

section Assembly

variable {d : ℕ} {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- Exact forward compression. The messages retain their original
bases, and all other internal registers have the actual coefficient-support
dimensions. The operational channel is preserved exactly. -/
theorem PureProtocol.exists_compressed_forward
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB) :
    ∃ r kA kB eA eB : ℕ, r = schmidtRank P.resource ∧
      kA ≤ d * r * Fintype.card μA ∧ kB ≤ d * r * Fintype.card μB ∧
      eA ≤ d * kA * Fintype.card μB ∧ eB ≤ d * kB * Fintype.card μA ∧
      ∃ Q : PureProtocol (Fin d) (Fin d) (Fin r) (Fin r) (Fin kA) (Fin kB)
        μA μB (Fin d) (Fin d) (Fin eA) (Fin eB),
        P.operationalChannel = Q.operationalChannel := by
  have hfac := exists_resource_support_factorization P.resource P.resource_unit
  generalize hr : schmidtRank P.resource = r at hfac
  obtain ⟨JA, JB, η, hJA, hJB, hη, hresource⟩ := hfac
  let VA0 := P.encA * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ JA)
  let VB0 := P.encB * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ JB)
  have hVA0 : IsIsometry VA0 := P.encA_isometry.mul (isIsometry_one.kronecker hJA)
  have hVB0 : IsIsometry VB0 := P.encB_isometry.mul (isIsometry_one.kronecker hJB)
  obtain ⟨kA, hkA, KA, VA, hKA, hA⟩ := exists_left_coefficient_factorization VA0
  obtain ⟨kB, hkB, KB, VB, hKB, hB⟩ := exists_left_coefficient_factorization VB0
  have hVA : IsIsometry VA :=
    ((hKA.kronecker isIsometry_one).mul_iff VA).mp (hA ▸ hVA0)
  have hVB : IsIsometry VB :=
    ((hKB.kronecker isIsometry_one).mul_iff VB).mp (hB ▸ hVB0)
  let DA0 := P.decA * (KA ⊗ₖ (1 : Matrix μB μB ℂ))
  let DB0 := P.decB * (KB ⊗ₖ (1 : Matrix μA μA ℂ))
  have hDA0 : IsIsometry DA0 := P.decA_isometry.mul (hKA.kronecker isIsometry_one)
  have hDB0 : IsIsometry DB0 := P.decB_isometry.mul (hKB.kronecker isIsometry_one)
  obtain ⟨eA, heA, EA, DA, hEA, hDA⟩ := exists_right_coefficient_factorization DA0
  obtain ⟨eB, heB, EB, DB, hEB, hDB⟩ := exists_right_coefficient_factorization DB0
  have hDA' : IsIsometry DA :=
    ((isIsometry_one.kronecker hEA).mul_iff DA).mp (hDA ▸ hDA0)
  have hDB' : IsIsometry DB :=
    ((isIsometry_one.kronecker hEB).mul_iff DB).mp (hDB ▸ hDB0)
  let Q : PureProtocol (Fin d) (Fin d) (Fin r) (Fin r) (Fin kA) (Fin kB)
      μA μB (Fin d) (Fin d) (Fin eA) (Fin eB) :=
    ⟨η, hη, VA, VB, hVA, hVB, DA, DB, hDA', hDB'⟩
  refine ⟨r, kA, kB, eA, eB, rfl, ?_, ?_, ?_, ?_, Q, ?_⟩
  · simpa only [Fintype.card_prod, Fintype.card_fin] using hkA
  · simpa only [Fintype.card_prod, Fintype.card_fin] using hkB
  · simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_assoc] using heA
  · simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_assoc] using heB
  · have hF : P.globalIsometry =
        (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ EA) ⊗ₖ
          ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ EB)) * Q.globalIsometry := by
      change NLQCLean.globalIsometry P.resource P.encA P.encB P.decA P.decB =
        _ * NLQCLean.globalIsometry η VA VB DA DB
      rw [hresource, globalIsometry_resource_inclusions]
      change NLQCLean.globalIsometry η VA0 VB0 P.decA P.decB = _
      rw [hA, hB, globalIsometry_private_inclusions]
      change NLQCLean.globalIsometry η VA VB DA0 DB0 = _
      rw [hDA, hDB]
      simp only [NLQCLean.globalIsometry, NLQCLean.decoder, Matrix.mul_kronecker_mul, Matrix.mul_assoc]
    have hFreg :
        P.globalIsometry.submatrix (outputRegroup (Fin d) (Fin d) εA εB) id =
          ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ (EA ⊗ₖ EB)) *
            Q.globalIsometry.submatrix
              (outputRegroup (Fin d) (Fin d) (Fin eA) (Fin eB)) id :=
      (congrArg (fun F : Matrix ((Fin d × εA) × (Fin d × εB)) (Fin d × Fin d) ℂ =>
        F.submatrix (outputRegroup (Fin d) (Fin d) εA εB) id) hF).trans
          (regroup_environment_inclusions EA EB Q.globalIsometry)
    change channelOf (P.globalIsometry.submatrix (outputRegroup (Fin d) (Fin d) εA εB) id) =
      channelOf (Q.globalIsometry.submatrix
        (outputRegroup (Fin d) (Fin d) (Fin eA) (Fin eB)) id)
    rw [hFreg]
    exact channelOf_environment_inclusion (EA ⊗ₖ EB) (hEA.kronecker hEB) _

end Assembly

/-- Finite-cardinality architectures with balanced logical registers. -/
abbrev FinProtocol (d : ℕ) (s : Fin 8 → ℕ) :=
  PureProtocol (Fin d) (Fin d) (Fin (s 0)) (Fin (s 1)) (Fin (s 2)) (Fin (s 3))
    (Fin (s 4)) (Fin (s 5)) (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7))

section FiniteRepresentative

variable {d : ℕ} {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- **Finite-family representative theorem.** Every original protocol
with charged rank/message footprint at most K has exactly the same channel
as a protocol on finite cardinality indices, all at most `d² K`. Its footprint
is still at most K. No bound on original private or resource dimensions is
assumed. The sharper actual-support bounds are in `exists_compressed_forward`.
The finite box used here may also contain additional architectures, which
are harmless for the qualitative compact-maximum argument. -/
theorem PureProtocol.exists_bounded_support_charged_fin_representative
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB)
    (hd : 2 ≤ d) (K : ℕ) (hK : P.HasFootprint K) :
    ∃ s : Fin 8 → ℕ, (∀ i, 0 < s i ∧ s i ≤ d ^ 2 * K) ∧
      s 0 * s 4 * s 5 ≤ K ∧
      ∃ Q : FinProtocol d s, Q.HasFootprint K ∧
        P.operationalChannel = Q.operationalChannel := by
  obtain ⟨r, kA, kB, eA, eB, hr, hkA, hkB, heA, heB, Q, hchan⟩ :=
    P.exists_compressed_forward
  let mA := Fintype.card μA
  let mB := Fintype.card μB
  have hdpos : 0 < d := by omega
  have hrpos : 0 < r := by
    have h := Q.resource_unit.card_pos
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    exact Nat.pos_of_mul_pos_right h
  have hencA : d * r ≤ kA * mA := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Q.encA_isometry.card_le
  have hencB : d * r ≤ kB * mB := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Q.encB_isometry.card_le
  have hka : 0 < kA := Nat.pos_of_mul_pos_right ((Nat.mul_pos hdpos hrpos).trans_le hencA)
  have hma : 0 < mA := Nat.pos_of_mul_pos_left ((Nat.mul_pos hdpos hrpos).trans_le hencA)
  have hkb : 0 < kB := Nat.pos_of_mul_pos_right ((Nat.mul_pos hdpos hrpos).trans_le hencB)
  have hmb : 0 < mB := Nat.pos_of_mul_pos_left ((Nat.mul_pos hdpos hrpos).trans_le hencB)
  have hdecA : kA * mB ≤ d * eA := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Q.decA_isometry.card_le
  have hdecB : kB * mA ≤ d * eB := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Q.decB_isometry.card_le
  have hea : 0 < eA := Nat.pos_of_mul_pos_left ((Nat.mul_pos hka hmb).trans_le hdecA)
  have heb : 0 < eB := Nat.pos_of_mul_pos_left ((Nat.mul_pos hkb hma).trans_le hdecB)
  have hfoot : r * mA * mB ≤ K := by
    have h := (hasFootprint_iff K P.resource).mp hK
    simpa only [← hr] using h
  have hrm : r * mA ≤ K := (Nat.le_mul_of_pos_right _ hmb).trans hfoot
  have hrK : r ≤ K := (Nat.le_mul_of_pos_right _ hma).trans hrm
  have hmAK : mA ≤ K := (Nat.le_mul_of_pos_left _ hrpos).trans hrm
  have hmBK : mB ≤ K := (Nat.le_mul_of_pos_left _ (Nat.mul_pos hrpos hma)).trans hfoot
  have hqa : kA * mB ≤ d * K := by
    calc
      kA * mB ≤ (d * r * mA) * mB := Nat.mul_le_mul_right mB hkA
      _ ≤ d * K := by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left d hfoot
  have hqb : kB * mA ≤ d * K := by
    calc
      kB * mA ≤ (d * r * mB) * mA := Nat.mul_le_mul_right mA hkB
      _ ≤ d * K := by
        simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          Nat.mul_le_mul_left d hfoot
  have hKbox : K ≤ d ^ 2 * K := Nat.le_mul_of_pos_left K (pow_pos hdpos 2)
  have hdKbox : d * K ≤ d ^ 2 * K := by
    simpa only [pow_two] using Nat.mul_le_mul_right K (Nat.le_mul_of_pos_right d hdpos)
  have hrbox := hrK.trans hKbox
  have hmabox := hmAK.trans hKbox
  have hmbbox := hmBK.trans hKbox
  have hkabox := ((Nat.le_mul_of_pos_right kA hmb).trans hqa).trans hdKbox
  have hkbbox := ((Nat.le_mul_of_pos_right kB hma).trans hqb).trans hdKbox
  have heabox : eA ≤ d ^ 2 * K := by
    calc
      eA ≤ d * (kA * mB) := by simpa only [Nat.mul_assoc] using heA
      _ ≤ d * (d * K) := Nat.mul_le_mul_left d hqa
      _ = d ^ 2 * K := by ring
  have hebbox : eB ≤ d ^ 2 * K := by
    calc
      eB ≤ d * (kB * mA) := by simpa only [Nat.mul_assoc] using heB
      _ ≤ d * (d * K) := Nat.mul_le_mul_left d hqb
      _ = d ^ 2 * K := by ring
  let s : Fin 8 → ℕ := ![r, r, kA, kB, mA, mB, eA, eB]
  let R : FinProtocol d s := Q.reindex (Equiv.refl _) (Equiv.refl _)
    (Equiv.refl _) (Equiv.refl _) (Fintype.equivFin μA).symm (Fintype.equivFin μB).symm
    (Equiv.refl _) (Equiv.refl _)
  refine ⟨s, ?_, ?_, R, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp only [s] <;>
      exact ⟨by assumption, by assumption⟩
  · exact hfoot
  · apply (hasFootprint_iff K R.resource).mpr
    have hrank : schmidtRank R.resource ≤ r := by
      have h := schmidtRank_le_card_left R.resource
      change schmidtRank R.resource ≤ Fintype.card (Fin r) at h
      simpa only [Fintype.card_fin] using h
    change schmidtRank R.resource * Fintype.card (Fin mA) * Fintype.card (Fin mB) ≤ K
    simp only [Fintype.card_fin]
    exact (Nat.mul_le_mul_right mB (Nat.mul_le_mul_right mA hrank)).trans hfoot
  · exact hchan.trans (Q.operationalChannel_reindex (Equiv.refl _) (Equiv.refl _)
      (Equiv.refl _) (Equiv.refl _) (Fintype.equivFin μA).symm (Fintype.equivFin μB).symm
      (Equiv.refl _) (Equiv.refl _)).symm

/-- A finite-cardinality representative with the original footprint and channel.
The stronger theorem also retains the support charge of the architecture. -/
theorem PureProtocol.exists_bounded_fin_representative
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB)
    (hd : 2 ≤ d) (K : ℕ) (hK : P.HasFootprint K) :
    ∃ s : Fin 8 → ℕ, (∀ i, 0 < s i ∧ s i ≤ d ^ 2 * K) ∧
      ∃ Q : FinProtocol d s, Q.HasFootprint K ∧
        P.operationalChannel = Q.operationalChannel := by
  obtain ⟨s, hs, _, Q, hQ, hchan⟩ :=
    P.exists_bounded_support_charged_fin_representative hd K hK
  exact ⟨s, hs, Q, hQ, hchan⟩

end FiniteRepresentative

end NLQCLean

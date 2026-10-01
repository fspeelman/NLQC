import NLQCLean.Models.ForwardWitness

/-!
# Relabeling the internal registers of a forward witness

Arbitrary finite register bases are replaced by `Fin` of their cardinalities.
These identities transport the six raw blocks along arbitrary equivalences,
preserving the sphere/Stiefel constraints and the global dilation. Logical
indices stay fixed, and the canonical exchange commutes with the relabeling.
-/

namespace NLQCLean

open Matrix
open scoped Kronecker

/-- Bijections preserve the unit-vector constraint, including empty types. -/
theorem IsUnitVector.comp_equiv {m n : Type*} [Fintype m] [Fintype n]
    {v : n → ℂ} (hv : IsUnitVector v) (e : m ≃ n) : IsUnitVector (v ∘ e) := by
  unfold IsUnitVector at *
  rw [show (∑ i, Complex.normSq ((v ∘ e) i)) = ∑ j, Complex.normSq (v j) from
    e.sum_comp (fun j => Complex.normSq (v j))]
  exact hv

/-- Independent row and column relabelings preserve rectangular isometries. -/
theorem IsIsometry.submatrix_equiv {m n m' n' : Type*}
    [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
    [DecidableEq n] [DecidableEq n'] {V : Matrix m n ℂ}
    (hV : IsIsometry V) (r : m' ≃ m) (c : n' ≃ n) :
    IsIsometry (V.submatrix r c) := by
  unfold IsIsometry at *
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hV,
    Matrix.submatrix_one_equiv]

/-- Environment insertion commutes with an environment basis equivalence. -/
theorem insertVector_reindex {ι ε ε' : Type*} [DecidableEq ι]
    (e : ε' ≃ ε) (g : ε → ℂ) :
    insertVector ι (g ∘ e) =
      (insertVector ι g).submatrix ((Equiv.refl ι).prodCongr e) id := by
  ext p q
  rfl

section Registers

variable {ιA ιB ιA' ιB' ρA ρB κA κB μA μB εA εB
    ρA₂ ρB₂ κA₂ κB₂ μA₂ μB₂ εA₂ εB₂ : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ιA'] [Fintype ιB']
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [Fintype ρA₂] [Fintype ρB₂] [Fintype κA₂] [Fintype κB₂]
variable [Fintype μA₂] [Fintype μB₂] [Fintype εA₂] [Fintype εB₂]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ιA'] [DecidableEq ιB']
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
variable [DecidableEq ρA₂] [DecidableEq ρB₂] [DecidableEq κA₂] [DecidableEq κB₂]
variable [DecidableEq μA₂] [DecidableEq μB₂] [DecidableEq εA₂] [DecidableEq εB₂]

variable (rA : ρA₂ ≃ ρA) (rB : ρB₂ ≃ ρB)
    (kA : κA₂ ≃ κA) (kB : κB₂ ≃ κB) (mA : μA₂ ≃ μA) (mB : μB₂ ≃ μB)
    (eA : εA₂ ≃ εA) (eB : εB₂ ≃ εB)

omit [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
  [Fintype ρA₂] [Fintype ρB₂] [DecidableEq ρA] [DecidableEq ρB]
  [DecidableEq ρA₂] [DecidableEq ρB₂] in
/-- Resource insertion commutes with relabeling the two resource bases. -/
theorem insertResource_reindex (η : ρA × ρB → ℂ) :
    insertResource ιA ιB (η ∘ rA.prodCongr rB) =
      (insertResource ιA ιB η).submatrix
        (((Equiv.refl ιA).prodCongr rA).prodCongr ((Equiv.refl ιB).prodCongr rB)) id := by
  ext p q
  rfl

omit [DecidableEq ρA] [DecidableEq ρB] [DecidableEq ρA₂] [DecidableEq ρB₂] in
/-- The encoded state uses exactly the canonical exchanged wire labels. -/
theorem encodedState_reindex (η : ρA × ρB → ℂ)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ) :
    encodedState (η ∘ rA.prodCongr rB)
        (VA.submatrix (kA.prodCongr mA) ((Equiv.refl ιA).prodCongr rA))
        (VB.submatrix (kB.prodCongr mB) ((Equiv.refl ιB).prodCongr rB)) =
      (encodedState η VA VB).submatrix
        ((kA.prodCongr mB).prodCongr (kB.prodCongr mA)) id := by
  simp only [encodedState, exchangeMatrix_mul, insertResource_reindex,
    kroneckerMap_submatrix_submatrix]
  have hmul := Matrix.submatrix_mul_equiv (VA ⊗ₖ VB) (insertResource ιA ιB η)
    ((kA.prodCongr mA).prodCongr (kB.prodCongr mB))
    (((Equiv.refl ιA).prodCongr rA).prodCongr ((Equiv.refl ιB).prodCongr rB)) id
  exact (congrArg (fun M : Matrix ((κA₂ × μA₂) × (κB₂ × μB₂)) (ιA × ιB) ℂ =>
    M.submatrix (exchangeEquiv κA₂ μA₂ κB₂ μB₂) id) hmul).trans (by
      ext p q
      rfl)

omit [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
  [Fintype εA₂] [Fintype εB₂] [DecidableEq ιA'] [DecidableEq ιB']
  [DecidableEq εA] [DecidableEq εB] [DecidableEq εA₂] [DecidableEq εB₂] in
omit [DecidableEq ρA] [DecidableEq ρB] [DecidableEq ρA₂] [DecidableEq ρB₂] in
/-- Global dilation relabeling; only the discarded output labels change. -/
theorem globalIsometry_reindex (η : ρA × ρB → ℂ)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ) :
    globalIsometry (η ∘ rA.prodCongr rB)
        (VA.submatrix (kA.prodCongr mA) ((Equiv.refl ιA).prodCongr rA))
        (VB.submatrix (kB.prodCongr mB) ((Equiv.refl ιB).prodCongr rB))
        (DA.submatrix ((Equiv.refl ιA').prodCongr eA) (kA.prodCongr mB))
        (DB.submatrix ((Equiv.refl ιB').prodCongr eB) (kB.prodCongr mA)) =
      (globalIsometry η VA VB DA DB).submatrix
        (((Equiv.refl ιA').prodCongr eA).prodCongr
          ((Equiv.refl ιB').prodCongr eB)) id := by
  simp only [globalIsometry, decoder, encodedState_reindex,
    kroneckerMap_submatrix_submatrix]
  exact Matrix.submatrix_mul_equiv _ _ _
    ((kA.prodCongr mB).prodCongr (kB.prodCongr mA)) _

/-- The six transported blocks, with logical indices unchanged. -/
def reindexForwardBlocks
    (x : ForwardBlocks ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB) :
    ForwardBlocks ιA ιB ρA₂ ρB₂ κA₂ κB₂ μA₂ μB₂ ιA' ιB' εA₂ εB₂ :=
  (x.1 ∘ rA.prodCongr rB, x.2.1 ∘ eA.prodCongr eB,
    x.2.2.1.submatrix (kA.prodCongr mA) ((Equiv.refl ιA).prodCongr rA),
    x.2.2.2.1.submatrix (kB.prodCongr mB) ((Equiv.refl ιB).prodCongr rB),
    x.2.2.2.2.1.submatrix ((Equiv.refl ιA').prodCongr eA) (kA.prodCongr mB),
    x.2.2.2.2.2.submatrix ((Equiv.refl ιB').prodCongr eB) (kB.prodCongr mA))

omit [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB] [Fintype εA₂] [Fintype εB₂] [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB] [DecidableEq εA₂] [DecidableEq εB₂] in
omit [DecidableEq ρA] [DecidableEq ρB] [DecidableEq ρA₂] [DecidableEq ρB₂] in
/-- The regrouped dilation changes only its environment row labels. -/
theorem globalIsometryRegrouped_reindex
    (x : ForwardBlocks ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB) :
    let y := reindexForwardBlocks rA rB kA kB mA mB eA eB x
    globalIsometryRegrouped y.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1 y.2.2.2.2.2 =
      (globalIsometryRegrouped x.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2).submatrix
        ((Equiv.refl (ιA' × ιB')).prodCongr (eA.prodCongr eB)) id := by
  dsimp only [reindexForwardBlocks]
  unfold globalIsometryRegrouped
  rw [globalIsometry_reindex]
  ext p q
  rfl

omit [DecidableEq εA] [DecidableEq εB] [DecidableEq εA₂] [DecidableEq εB₂] in
omit [DecidableEq ρA] [DecidableEq ρB] [DecidableEq ρA₂] [DecidableEq ρB₂] in
/-- Relabeling invariance of the raw overlap, hence of its purity. -/
theorem forwardOverlapOn_reindex
    (x : ForwardBlocks ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB) :
    forwardOverlapOn (reindexForwardBlocks rA rB kA kB mA mB eA eB x) =
      forwardOverlapOn x := by
  have h (g : εA × εB → ℂ) :
      insertVector (ιA' × ιB') (g ∘ eA.prodCongr eB) =
        (insertVector (ιA' × ιB') g).submatrix
          ((Equiv.refl (ιA' × ιB')).prodCongr (eA.prodCongr eB)) id := by
    ext p q
    rfl
  unfold forwardOverlapOn reindexForwardBlocks forwardOverlap globalIsometryRegrouped
  dsimp only [Prod.fst, Prod.snd]
  rw [globalIsometry_reindex, h, Matrix.conjTranspose_submatrix]
  have hreg (F : Matrix ((ιA' × εA) × (ιB' × εB)) (ιA × ιB) ℂ) :
      (F.submatrix (((Equiv.refl ιA').prodCongr eA).prodCongr
          ((Equiv.refl ιB').prodCongr eB)) id).submatrix
        (outputRegroup ιA' ιB' εA₂ εB₂) id =
      (F.submatrix (outputRegroup ιA' ιB' εA εB) id).submatrix
        ((Equiv.refl (ιA' × ιB')).prodCongr (eA.prodCongr eB)) id := by
    ext p q
    rfl
  rw [hreg, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]

end Registers

/-- Relabeling a discarded environment preserves the operational channel. -/
theorem channelOf_reindex_environment {ι κ ε ε' : Type*}
    [Fintype ι] [Fintype κ] [Fintype ε] [Fintype ε']
    [DecidableEq ι] [DecidableEq κ] [DecidableEq ε] [DecidableEq ε']
    (e : ε' ≃ ε) (F : Matrix (κ × ε) ι ℂ) :
    channelOf (F.submatrix ((Equiv.refl κ).prodCongr e) id) = channelOf F := by
  ext M i j
  let r := (Equiv.refl κ).prodCongr e
  have hleft : F.submatrix r id * M = (F * M).submatrix r id := by
    simpa only [Equiv.coe_refl, Matrix.submatrix_id_id] using
      Matrix.submatrix_mul_equiv F M r (Equiv.refl ι) id
  have hprod : F.submatrix r id * M * (F.submatrix r id)ᴴ =
      (F * M * Fᴴ).submatrix r r := by
    rw [Matrix.conjTranspose_submatrix, hleft]
    exact Matrix.submatrix_mul_equiv _ _ r (Equiv.refl ι) r
  change (∑ a : ε', (F.submatrix r id * M * (F.submatrix r id)ᴴ) (i, a) (j, a)) =
    ∑ a : ε, (F * M * Fᴴ) (i, a) (j, a)
  rw [hprod]
  exact e.sum_comp (fun a => (F * M * Fᴴ) (i, a) (j, a))

section ProtocolReindex

variable {ιA ιB ιA' ιB' ρA ρB κA κB μA μB εA εB
    ρA₂ ρB₂ κA₂ κB₂ μA₂ μB₂ εA₂ εB₂ : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ιA'] [Fintype ιB']
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [Fintype ρA₂] [Fintype ρB₂] [Fintype κA₂] [Fintype κB₂]
variable [Fintype μA₂] [Fintype μB₂] [Fintype εA₂] [Fintype εB₂]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ιA'] [DecidableEq ιB']
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
variable [DecidableEq ρA₂] [DecidableEq ρB₂] [DecidableEq κA₂] [DecidableEq κB₂]
variable [DecidableEq μA₂] [DecidableEq μB₂] [DecidableEq εA₂] [DecidableEq εB₂]

/-- Transport a physical protocol along equivalences of its internal registers. -/
def PureProtocol.reindex
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB)
    (rA : ρA₂ ≃ ρA) (rB : ρB₂ ≃ ρB) (kA : κA₂ ≃ κA) (kB : κB₂ ≃ κB)
    (mA : μA₂ ≃ μA) (mB : μB₂ ≃ μB) (eA : εA₂ ≃ εA) (eB : εB₂ ≃ εB) :
    PureProtocol ιA ιB ρA₂ ρB₂ κA₂ κB₂ μA₂ μB₂ ιA' ιB' εA₂ εB₂ where
  resource := P.resource ∘ rA.prodCongr rB
  resource_unit := P.resource_unit.comp_equiv (rA.prodCongr rB)
  encA := P.encA.submatrix (kA.prodCongr mA) ((Equiv.refl ιA).prodCongr rA)
  encB := P.encB.submatrix (kB.prodCongr mB) ((Equiv.refl ιB).prodCongr rB)
  encA_isometry := P.encA_isometry.submatrix_equiv _ _
  encB_isometry := P.encB_isometry.submatrix_equiv _ _
  decA := P.decA.submatrix ((Equiv.refl ιA').prodCongr eA) (kA.prodCongr mB)
  decB := P.decB.submatrix ((Equiv.refl ιB').prodCongr eB) (kB.prodCongr mA)
  decA_isometry := P.decA_isometry.submatrix_equiv _ _
  decB_isometry := P.decB_isometry.submatrix_equiv _ _

/-- Internal basis labels do not change a physical protocol's channel. -/
theorem PureProtocol.operationalChannel_reindex
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB)
    (rA : ρA₂ ≃ ρA) (rB : ρB₂ ≃ ρB) (kA : κA₂ ≃ κA) (kB : κB₂ ≃ κB)
    (mA : μA₂ ≃ μA) (mB : μB₂ ≃ μB) (eA : εA₂ ≃ εA) (eB : εB₂ ≃ εB) :
    (P.reindex rA rB kA kB mA mB eA eB).operationalChannel = P.operationalChannel := by
  let x : ForwardBlocks ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB :=
    (P.resource, 0, P.encA, P.encB, P.decA, P.decB)
  let Q := P.reindex rA rB kA kB mA mB eA eB
  have hF : globalIsometryRegrouped Q.resource Q.encA Q.encB Q.decA Q.decB =
      (globalIsometryRegrouped P.resource P.encA P.encB P.decA P.decB).submatrix
        ((Equiv.refl (ιA' × ιB')).prodCongr (eA.prodCongr eB)) id :=
    globalIsometryRegrouped_reindex rA rB kA kB mA mB eA eB x
  change channelOf (globalIsometryRegrouped Q.resource Q.encA Q.encB Q.decA Q.decB) = _
  rw [hF]
  exact channelOf_reindex_environment (eA.prodCongr eB) _

end ProtocolReindex

end NLQCLean

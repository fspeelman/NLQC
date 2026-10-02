/-
The one-round architecture record and the global Stinespring isometry.
-/
import NLQCLean.Rigidity.FrozenDilation

/-!
# One simultaneous round: the architecture record and `eq:global-isometry`

This module records the finite coherent architecture of the snapshot
(L428-472) and assembles the global Stinespring isometry

  `F = (D_A ⊗ D_B) Ex (V_A ⊗ V_B) J_η`   (**eq:global-isometry**, L456-460).

The pieces are kept separate on purpose.  The paper's proof of
`prop:exact-velocity` (L812-853) works with

  `Y = Ex (V_A ⊗ V_B) J_η`,  `Dec = D_A ⊗ D_B`,  `F = Dec Y`

throughout, so `NLQCLean.encodedState` and `NLQCLean.decoder` are named
definitions and `NLQCLean.globalIsometry` is literally their product.

## Registers and the grouping convention

Twelve index types, all finite:

| paper | Lean | role |
|---|---|---|
| `H_A`, `H_B` | `ιA`, `ιB` | logical inputs (L429-430) |
| `R_A`, `R_B` | `ρA`, `ρB` | shared resource (L432-433) |
| `K_A`, `K_B` | `κA`, `κB` | kept encoder output (L434-437) |
| `M_A`, `M_B` | `μA`, `μB` | messages (L434-437) |
| `H_{A'}`, `H_{B'}` | `ιA'`, `ιB'` | logical outputs (L440-443) |
| `E_A`, `E_B` | `εA`, `εB` | private environments (L440-443) |

`Q_A := K_A ⊗ M_B` and `Q_B := K_B ⊗ M_A` (L440-441) are written out as
`κA × μB` and `κB × μA` rather than introduced as type synonyms, because
`prop:protocol-cross-gram` later forms a `Sum` on top of them.

Registers are grouped **by laboratory** (L454), exactly as in
`NLQCLean/Rigidity/Compression.lean`.  This is what makes the assembly
reassociation-free: with

  `V_A : Matrix (κA × μA) (ιA × ρA) ℂ`,  `V_B : Matrix (κB × μB) (ιB × ρB) ℂ`

the Kronecker product `V_A ⊗ₖ V_B` has row index `(κA × μA) × (κB × μB)` and
column index `(ιA × ρA) × (ιB × ρB)`, which is *literally* the codomain index
of `NLQCLean.insertResource ιA ιB η`.  The **only** reindexing inside `F` is
the exchange permutation itself; no `Equiv.prodAssoc` or `Equiv.prodComm`
appears anywhere in the construction.

`ιA'` and `ιB'` are kept genuinely distinct from `ιA` and `ιB`.  The paper
allows `H_{A'}` to be any output register (L440-446), and for a measurement it
is the coherent outcome label; identifying them would silently narrow the
architecture.

## The exchange permutation is a definition, not a field

Snapshot L438-439 fixes *one* permutation `Ex` that exchanges `M_A` and
`M_B`.  Once the registers are fixed, that permutation is canonical, and
`NLQCLean.exchangeMatrix` is it: the permutation matrix of

  `(K_A ⊗ M_B) ⊗ (K_B ⊗ M_A) ≃ (K_A ⊗ M_A) ⊗ (K_B ⊗ M_B)`.

It is deliberately *not* an arbitrary unitary field of the architecture
record, for two reasons.

* Nothing downstream inspects an entry of `Ex`.  `prop:exact-velocity`
  (L836-841) uses only `Ex† Ex = I` and the fact that `Ex` does not vary along
  the path — "the architecture fixes ... the exchange permutation" (L446-448).
* `thm:finite-orbit` (L916-918) counts "finite register dimensions and
  exchange permutations", which is a *countable* set.  An arbitrary unitary
  field would destroy that count.

Any further relabelling inside `M_A` or `M_B` is absorbed into `V_X` and
`D_X`, which the paper allows to depend arbitrarily on the target (L446-448).
Likewise, finite classical processing needs no field of its own: L462-464 puts
it inside `V_X`, `D_X` and `E_X` by coherently copying labels into the
discarded environment.

## Caution for the PVM task predicate

`eq:frozen-pvm` (L655-661) type-checks against this architecture only when
`ιA' = ιB' = δ` *and* `δ` is the joint outcome label, i.e. `δ = ιA × ιB`:
"for a measurement, `H_{X'}` includes the coherent outcome label" (L445).
The PVM task is defined at this specialized instantiation.
-/

namespace NLQCLean

open Matrix
open scoped Kronecker

section SubmatrixCancel

/-- Restricting rows along a bijection is injective on matrices.  Used to
transport an identity proved in the `channelOf` grouping back to the
by-laboratory grouping. -/
theorem eq_of_submatrix_equiv_id {m m' n : Type*} (e : m' ≃ m)
    {A B : Matrix m n ℂ} (h : A.submatrix e id = B.submatrix e id) : A = B := by
  ext i j
  have h2 := congrArg (fun M : Matrix m' n ℂ => M (e.symm i) j) h
  simpa using h2

end SubmatrixCancel

section Exchange

variable (κA μA κB μB : Type*)

/-- The exchange of the two message registers (snapshot L438-439):
`(K_A ⊗ M_B) ⊗ (K_B ⊗ M_A) ≃ (K_A ⊗ M_A) ⊗ (K_B ⊗ M_B)`.

Note that this is *not* the middle-two transposition
`NLQCLean.outputRegroup`; it swaps the two second components. -/
def exchangeEquiv : (κA × μB) × (κB × μA) ≃ (κA × μA) × (κB × μB) where
  toFun p := ((p.1.1, p.2.2), (p.2.1, p.1.2))
  invFun q := ((q.1.1, q.2.2), (q.2.1, q.1.2))
  left_inv := by rintro ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl
  right_inv := by rintro ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl

@[simp] theorem exchangeEquiv_apply (p : (κA × μB) × (κB × μA)) :
    exchangeEquiv κA μA κB μB p = ((p.1.1, p.2.2), (p.2.1, p.1.2)) := rfl

variable [DecidableEq κA] [DecidableEq μA] [DecidableEq κB] [DecidableEq μB]

/-- The fixed exchange permutation `Ex` of snapshot L438-439, as a matrix. -/
def exchangeMatrix :
    Matrix ((κA × μB) × (κB × μA)) ((κA × μA) × (κB × μB)) ℂ :=
  (1 : Matrix ((κA × μA) × (κB × μB)) ((κA × μA) × (κB × μB)) ℂ).submatrix
    (exchangeEquiv κA μA κB μB) id

theorem exchangeMatrix_def :
    exchangeMatrix κA μA κB μB
      = (1 : Matrix ((κA × μA) × (κB × μB)) ((κA × μA) × (κB × μB)) ℂ).submatrix
          (exchangeEquiv κA μA κB μB) id := rfl

@[simp] theorem exchangeMatrix_apply (p : (κA × μB) × (κB × μA))
    (q : (κA × μA) × (κB × μB)) :
    exchangeMatrix κA μA κB μB p q
      = if exchangeEquiv κA μA κB μB p = q then 1 else 0 := rfl

variable [Fintype κA] [Fintype μA] [Fintype κB] [Fintype μB]

/-- Left multiplication by `Ex` is a row reindexing: `Ex M = M ∘ Ex`. -/
theorem exchangeMatrix_mul {ν : Type*}
    (M : Matrix ((κA × μA) × (κB × μB)) ν ℂ) :
    exchangeMatrix κA μA κB μB * M = M.submatrix (exchangeEquiv κA μA κB μB) id := by
  ext p j
  rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem (exchangeEquiv κA μA κB μB p)
    (Finset.mem_univ _)
    (fun q _ hq => by rw [exchangeMatrix_apply, ite_eq_right (Ne.symm hq), zero_mul])]
  simp

/-- `Ex† Ex = I`: the exchange permutation is an isometry.  This is all that
`prop:exact-velocity` (L836-841) uses about it. -/
theorem isIsometry_exchangeMatrix : IsIsometry (exchangeMatrix κA μA κB μB) := by
  show (exchangeMatrix κA μA κB μB)ᴴ * exchangeMatrix κA μA κB μB = 1
  rw [exchangeMatrix_def, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
    Matrix.submatrix_mul_equiv, Matrix.one_mul, Matrix.submatrix_id_id]

/-- `Ex Ex† = I`: the exchange permutation is also a coisometry, so it can be
cancelled from either side. -/
theorem exchangeMatrix_mul_conjTranspose :
    exchangeMatrix κA μA κB μB * (exchangeMatrix κA μA κB μB)ᴴ = 1 := by
  rw [exchangeMatrix_mul]
  ext p q
  have hEq : ((exchangeMatrix κA μA κB μB)ᴴ).submatrix
        (exchangeEquiv κA μA κB μB) id p q
      = star (if exchangeEquiv κA μA κB μB q = exchangeEquiv κA μA κB μB p
              then (1 : ℂ) else 0) := rfl
  rw [hEq]
  rcases eq_or_ne p q with rfl | h
  · simp
  · have hne : ¬ (exchangeEquiv κA μA κB μB q = exchangeEquiv κA μA κB μB p) :=
      fun hh => h (((exchangeEquiv κA μA κB μB).injective hh).symm)
    rw [ite_eq_right hne, star_zero, Matrix.one_apply_ne h]

end Exchange

section OutputRegroup

variable (ιA' ιB' εA εB : Type*)

/-- The middle-two transposition
`(H_{A'} ⊗ H_{B'}) ⊗ (E_A ⊗ E_B) ≃ (H_{A'} ⊗ E_A) ⊗ (H_{B'} ⊗ E_B)`
relating the paper's by-laboratory output grouping (L454) to the
system-then-environment grouping that `NLQCLean.channelOf` requires
(L461-463).

This is a genuinely different permutation from
`NLQCLean.exchangeEquiv`; it is the only other reindexing in the model. -/
def outputRegroup : (ιA' × ιB') × (εA × εB) ≃ (ιA' × εA) × (ιB' × εB) :=
  Equiv.prodProdProdComm ιA' ιB' εA εB

@[simp] theorem outputRegroup_apply (p : (ιA' × ιB') × (εA × εB)) :
    outputRegroup ιA' ιB' εA εB p = ((p.1.1, p.2.1), (p.1.2, p.2.2)) := rfl

end OutputRegroup

section Architecture

variable {ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]

/-- `Y = Ex (V_A ⊗ V_B) J_η`, the state after encoding and message exchange
(snapshot L813-815).  `prop:exact-velocity` differentiates exactly this. -/
def encodedState (η : ρA × ρB → ℂ)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ) (VB : Matrix (κB × μB) (ιB × ρB) ℂ) :
    Matrix ((κA × μB) × (κB × μA)) (ιA × ιB) ℂ :=
  exchangeMatrix κA μA κB μB * ((VA ⊗ₖ VB) * insertResource ιA ιB η)

/-- `Dec = D_A ⊗ D_B`, the joint decoder (snapshot L816). -/
def decoder (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ) :
    Matrix ((ιA' × εA) × (ιB' × εB)) ((κA × μB) × (κB × μA)) ℂ :=
  DA ⊗ₖ DB

/-- **eq:global-isometry** (snapshot L456-460):
`F = (D_A ⊗ D_B) Ex (V_A ⊗ V_B) J_η`, written as `F = Dec Y` (L818) in the
by-laboratory output grouping `(H_{A'} ⊗ E_A) ⊗ (H_{B'} ⊗ E_B)`. -/
def globalIsometry (η : ρA × ρB → ℂ)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ) (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ) (DB : Matrix (ιB' × εB) (κB × μA) ℂ) :
    Matrix ((ιA' × εA) × (ιB' × εB)) (ιA × ιB) ℂ :=
  decoder DA DB * encodedState η VA VB

omit [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB] [DecidableEq ρA] [DecidableEq ρB] [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB] in
theorem globalIsometry_eq (η : ρA × ρB → ℂ)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ) (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ) (DB : Matrix (ιB' × εB) (κB × μA) ℂ) :
    globalIsometry η VA VB DA DB
      = (DA ⊗ₖ DB) * (exchangeMatrix κA μA κB μB
          * ((VA ⊗ₖ VB) * insertResource ιA ιB η)) := rfl

/-- `Y` is an isometry. -/
theorem isIsometry_encodedState {η : ρA × ρB → ℂ} (hη : IsUnitVector η)
    {VA : Matrix (κA × μA) (ιA × ρA) ℂ} {VB : Matrix (κB × μB) (ιB × ρB) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) :
    IsIsometry (encodedState η VA VB) :=
  (isIsometry_exchangeMatrix κA μA κB μB).mul
    ((hVA.kronecker hVB).mul (isIsometry_insertResource η hη))

omit [Fintype κA] [Fintype μB] [DecidableEq ιA'] [DecidableEq εA] in
/-- `Dec` is an isometry. -/
theorem isIsometry_decoder {DA : Matrix (ιA' × εA) (κA × μB) ℂ}
    {DB : Matrix (ιB' × εB) (κB × μA) ℂ}
    (hDA : IsIsometry DA) (hDB : IsIsometry DB) : IsIsometry (decoder DA DB) :=
  hDA.kronecker hDB

omit [DecidableEq ιA'] [DecidableEq εA] in
/-- The global isometry of eq:global-isometry is a
product of four isometries, one for each factor of `F = Dec Ex (V_A ⊗ V_B)
J_η`.  The only nontrivial input is that `J_η` is an isometry, which is where
the unit-norm hypothesis on the shared state (L449-450) is consumed. -/
theorem isIsometry_globalIsometry {η : ρA × ρB → ℂ} (hη : IsUnitVector η)
    {VA : Matrix (κA × μA) (ιA × ρA) ℂ} {VB : Matrix (κB × μB) (ιB × ρB) ℂ}
    {DA : Matrix (ιA' × εA) (κA × μB) ℂ} {DB : Matrix (ιB' × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB) :
    IsIsometry (globalIsometry η VA VB DA DB) :=
  (isIsometry_decoder hDA hDB).mul (isIsometry_encodedState hη hVA hVB)

/-- The global isometry in the system-then-environment grouping demanded by
`NLQCLean.channelOf`: the same matrix, rows reindexed by
`NLQCLean.outputRegroup`. -/
def globalIsometryRegrouped (η : ρA × ρB → ℂ)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ) (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ) (DB : Matrix (ιB' × εB) (κB × μA) ℂ) :
    Matrix ((ιA' × ιB') × (εA × εB)) (ιA × ιB) ℂ :=
  (globalIsometry η VA VB DA DB).submatrix (outputRegroup ιA' ιB' εA εB) id

/-- **The operational channel** (snapshot L461-462): "Discarding the final
environment gives the operational channel."  The environment discarded is
`E_A ⊗ E_B`; the retained output is `H_{A'} ⊗ H_{B'}`. -/
def operationalChannel (η : ρA × ρB → ℂ)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ) (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ) (DB : Matrix (ιB' × εB) (κB × μA) ℂ) :
    Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ] Matrix (ιA' × ιB') (ιA' × ιB') ℂ :=
  channelOf (globalIsometryRegrouped η VA VB DA DB)

end Architecture

section FrozenBridge

variable {ιA' ιB' εA εB : Type*}
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]

omit [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB] [DecidableEq εA] [DecidableEq εB] in
/-- The environment-insertion bridge to `NLQCLean.Rigidity.FrozenDilation`: the
minimal environment insertion `J_γ` of the `channelOf` grouping is the
by-laboratory `NLQCLean.insertResource` with the resource types instantiated
to the two private environments, read across `NLQCLean.outputRegroup`. -/
theorem insertVector_eq_insertResource_submatrix (γ : εA × εB → ℂ) :
    insertVector (ιA' × ιB') γ
      = (insertResource ιA' ιB' γ).submatrix (outputRegroup ιA' ιB' εA εB) id := by
  ext p k
  rw [Matrix.submatrix_apply, insertVector_apply, insertResource_apply]
  by_cases h1 : p.1.1 = k.1 <;> by_cases h2 : p.1.2 = k.2 <;>
    simp [outputRegroup_apply, Prod.ext_iff, h1, h2]

end FrozenBridge

section FrozenGlobal

variable {ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]

omit [DecidableEq ρA] [DecidableEq ρB] in
omit [DecidableEq εA] [DecidableEq εB] in
/-- **`lem:frozen-dilations` (i) at eq:global-isometry.**

If the operational channel of the architecture is exactly `Ad_U` for a unitary
`U`, then there is a **single** unit vector `γ ∈ E_A ⊗ E_B`, independent of
the logical input, with

  `F = J_γ U`

in the by-laboratory grouping, where `J_γ` is
`NLQCLean.insertResource ι_{A'} ι_{B'} γ`.  This is the form
`prop:exact-velocity` (L818-826) consumes: `G = J_γ` and `T = U`.

`γ` is allowed to move when the *protocol* moves (L640-642); it is constant
only in the logical input, which is what the single `∃` records. -/
theorem exists_frozen_globalIsometry [Nonempty ιA] [Nonempty ιB]
    {η : ρA × ρB → ℂ}
    {VA : Matrix (κA × μA) (ιA × ρA) ℂ} {VB : Matrix (κB × μB) (ιB × ρB) ℂ}
    {DA : Matrix (ιA' × εA) (κA × μB) ℂ} {DB : Matrix (ιB' × εB) (κB × μA) ℂ}
    {U : Matrix (ιA' × ιB') (ιA × ιB) ℂ}
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hchan : operationalChannel η VA VB DA DB = adConj U) :
    ∃ γ : εA × εB → ℂ, IsUnitVector γ ∧
      globalIsometry η VA VB DA DB = insertResource ιA' ιB' γ * U := by
  have hchan' : channelOf (globalIsometryRegrouped η VA VB DA DB) = adConj U := hchan
  obtain ⟨γ, hγ, hFeq⟩ := exists_frozen_unitary hU hU' hchan'
  refine ⟨γ, hγ, ?_⟩
  refine eq_of_submatrix_equiv_id (outputRegroup ιA' ιB' εA εB) ?_
  rw [show (globalIsometry η VA VB DA DB).submatrix (outputRegroup ιA' ιB' εA εB) id
      = globalIsometryRegrouped η VA VB DA DB from rfl, hFeq,
    insertVector_eq_insertResource_submatrix,
    Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.submatrix_id_id]

end FrozenGlobal

section Packaging

/-- A **pure-resource one-round architecture** (snapshot L428-450).

Only operational data is stored:
the shared resource vector with its unit-norm condition (L449-450), the two
encoder isometries (L434-437), and the two decoder isometries (L440-443).
The exchange permutation is *not* a field — see the module docstring — and
neither is any classical-processing map, since L462-464 places finite
classical processing inside `V_X`, `D_X` and `E_X`.

The twelve register index types are parameters, fixed across the families
of protocols differentiated in `prop:exact-velocity` (L786-790). -/
structure PureProtocol (ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB : Type*)
    [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
    [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
    [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
    [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
    [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
    [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB] where
  /-- The shared pure resource `η ∈ R_A ⊗ R_B` (snapshot L432-433, L449). -/
  resource : ρA × ρB → ℂ
  /-- `η` is a unit vector (snapshot L449). -/
  resource_unit : IsUnitVector resource
  /-- `V_A : H_A ⊗ R_A → K_A ⊗ M_A` (snapshot L434-435). -/
  encA : Matrix (κA × μA) (ιA × ρA) ℂ
  /-- `V_B : H_B ⊗ R_B → K_B ⊗ M_B` (snapshot L436-437). -/
  encB : Matrix (κB × μB) (ιB × ρB) ℂ
  /-- `V_A` is an isometry (snapshot L433-434). -/
  encA_isometry : IsIsometry encA
  /-- `V_B` is an isometry (snapshot L433-434). -/
  encB_isometry : IsIsometry encB
  /-- `D_A : Q_A = K_A ⊗ M_B → H_{A'} ⊗ E_A` (snapshot L440-441). -/
  decA : Matrix (ιA' × εA) (κA × μB) ℂ
  /-- `D_B : Q_B = K_B ⊗ M_A → H_{B'} ⊗ E_B` (snapshot L442-443). -/
  decB : Matrix (ιB' × εB) (κB × μA) ℂ
  /-- `D_A` is an isometry (snapshot L439-440). -/
  decA_isometry : IsIsometry decA
  /-- `D_B` is an isometry (snapshot L439-440). -/
  decB_isometry : IsIsometry decB

namespace PureProtocol

variable {ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]
variable (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB)

/-- `Y = Ex (V_A ⊗ V_B) J_η` of the protocol (snapshot L813-815). -/
def encodedState : Matrix ((κA × μB) × (κB × μA)) (ιA × ιB) ℂ :=
  NLQCLean.encodedState P.resource P.encA P.encB

/-- `Dec = D_A ⊗ D_B` of the protocol (snapshot L816). -/
def decoder : Matrix ((ιA' × εA) × (ιB' × εB)) ((κA × μB) × (κB × μA)) ℂ :=
  NLQCLean.decoder P.decA P.decB

/-- **eq:global-isometry** for the protocol (snapshot L456-460). -/
def globalIsometry : Matrix ((ιA' × εA) × (ιB' × εB)) (ιA × ιB) ℂ :=
  NLQCLean.globalIsometry P.resource P.encA P.encB P.decA P.decB

/-- The operational channel of the protocol (snapshot L461-462). -/
def operationalChannel :
    Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ] Matrix (ιA' × ιB') (ιA' × ιB') ℂ :=
  NLQCLean.operationalChannel P.resource P.encA P.encB P.decA P.decB

theorem globalIsometry_eq_decoder_mul_encodedState :
    P.globalIsometry = P.decoder * P.encodedState := rfl

/-- The global isometry of a protocol is an isometry. -/
theorem isIsometry_globalIsometry : IsIsometry P.globalIsometry :=
  NLQCLean.isIsometry_globalIsometry P.resource_unit P.encA_isometry P.encB_isometry
    P.decA_isometry P.decB_isometry

/-- **`lem:frozen-dilations` (i) for a protocol.**  A pure-resource one-round
protocol that implements `Ad_U` exactly has

  `F = J_γ U`

for one unit vector `γ` on the discarded environment `E_A ⊗ E_B`, in the
by-laboratory grouping used by `lem:shared-state-compression`. -/
theorem exists_frozen [Nonempty ιA] [Nonempty ιB]
    {U : Matrix (ιA' × ιB') (ιA × ιB) ℂ}
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hchan : P.operationalChannel = adConj U) :
    ∃ γ : εA × εB → ℂ, IsUnitVector γ ∧
      P.globalIsometry = insertResource ιA' ιB' γ * U :=
  exists_frozen_globalIsometry hU hU' hchan

end PureProtocol

end Packaging

end NLQCLean

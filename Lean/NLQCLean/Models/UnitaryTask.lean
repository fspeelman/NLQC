/-
The exact unitary task for a one-round protocol.
-/
import NLQCLean.Models.Resource

/-!
# The unitary task

The first of the paper's two exact target classes (snapshot §2.2, L474-497):
the target unitary `U` maps `H_A ⊗ H_B` to the output copies
`H_{A'} ⊗ H_{B'}`, and "its channel is `Ad_U(ρ) = U ρ U^†`" (L477-478).  A
protocol *performs* the task exactly when its operational channel — the
channel of eq:global-isometry after discarding `E_A ⊗ E_B` (L461-462) — is
that channel on the nose.

`NLQCLean.PureProtocol.PerformsUnitary` is definitionally the hypothesis
`hchan` already consumed by `NLQCLean.PureProtocol.exists_frozen`, so
`NLQCLean.PureProtocol.exists_frozen_of_performsUnitary` restates nothing: it
is the same theorem read through the task predicate.

## Extraction of the frozen witness

`lem:frozen-dilations` (i) produces `γ` from a bare existential.  That is not
enough for `prop:exact-velocity` (L786-810), which *differentiates a family
of protocols*: the identity `G^† Ġ = ⟨γ|γ̇⟩ I` of eq:output-compression
(L845-852) is meaningless for a witness picked by `Classical.choice` at each
parameter value.

`NLQCLean.frozen_unitary_witness_eq` removes the choice.  It exhibits `γ` as
an explicit entry of `F U^†`,

  `γ(e_A, e_B) = (F U^†)_{((k_A,e_A),(k_B,e_B)),\,(k_A,k_B)}`

for *any* pair of output labels `(k_A, k_B)`, hence as a **linear** functional
of `F`.  A family `t ↦ F(t)` that is differentiable in the Frobenius norm
therefore has a differentiable `γ(t)`, and
`NLQCLean.frozen_unitary_witness_unique` shows there is nothing else it could
be.
-/

namespace NLQCLean

open Matrix

section UnitaryTarget

variable {ιA ιB ιA' ιB' : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ιA'] [Fintype ιB']
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ιA'] [DecidableEq ιB']

/-- A **unitary target** `U : H_A ⊗ H_B → H_{A'} ⊗ H_{B'}` (snapshot
L474-478).  The input and output logical spaces are distinct types of the
same dimension, so `U` is a rectangular matrix and unitarity is recorded as
the two-sided condition rather than through `Matrix.unitaryGroup`. -/
structure UnitaryTarget (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) : Prop where
  /-- `U^† U = I`. -/
  conjTranspose_mul_self : Uᴴ * U = 1
  /-- `U U^† = I`. -/
  self_mul_conjTranspose : U * Uᴴ = 1

theorem UnitaryTarget.isIsometry {U : Matrix (ιA' × ιB') (ιA × ιB) ℂ}
    (h : UnitaryTarget U) : IsIsometry U := h.conjTranspose_mul_self

end UnitaryTarget

section Task

variable {ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]

/-- **The exact unitary task** for the architecture of eq:global-isometry
(snapshot L456-462 with L477-478): the operational channel obtained by
discarding `E_A ⊗ E_B` is exactly `Ad_U`.

No condition is placed on the discarded environment; that it is nevertheless
frozen is the content of `lem:frozen-dilations` (i). -/
def PerformsUnitary (η : ρA × ρB → ℂ)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ) (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ) (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) : Prop :=
  operationalChannel η VA VB DA DB = adConj U

/-- The exact unitary task for a pure-resource protocol. -/
def PureProtocol.PerformsUnitary
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) : Prop :=
  P.operationalChannel = adConj U

theorem PureProtocol.performsUnitary_iff
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) :
    P.PerformsUnitary U
      ↔ NLQCLean.PerformsUnitary P.resource P.encA P.encB P.decA P.decB U :=
  Iff.rfl

/-- **`lem:frozen-dilations` (i) for a protocol performing the unitary
task** (snapshot L649-653).  This is `NLQCLean.PureProtocol.exists_frozen`
read through the task predicate; nothing is restated. -/
theorem PureProtocol.exists_frozen_of_performsUnitary [Nonempty ιA] [Nonempty ιB]
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB)
    {U : Matrix (ιA' × ιB') (ιA × ιB) ℂ} (hU : UnitaryTarget U)
    (htask : P.PerformsUnitary U) :
    ∃ γ : εA × εB → ℂ, IsUnitVector γ ∧
      P.globalIsometry = insertResource ιA' ιB' γ * U :=
  P.exists_frozen hU.conjTranspose_mul_self hU.self_mul_conjTranspose htask

end Task

section Witness

variable {ιA ιB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ιA'] [Fintype ιB']
variable [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ιA'] [DecidableEq ιB']
variable [DecidableEq εA] [DecidableEq εB]

omit [DecidableEq ιA] [DecidableEq ιB] in
omit [Fintype εA] [Fintype εB] [DecidableEq εA] [DecidableEq εB] in
/-- **The frozen environment vector is an explicit linear functional of `F`.**

If `F = J_γ U` (eq:frozen-unitary, snapshot L649-653) with `U` a unitary
target, then for *every* pair of output labels `(k_A, k_B)`

  `γ(e_A, e_B) = (F U^†)_{((k_A,e_A),(k_B,e_B)),\,(k_A,k_B)}`.

Two consequences matter for `prop:exact-velocity` (L786-810): the right-hand
side does not depend on the choice of `(k_A, k_B)`, so `γ` is *unique*; and
it is linear in `F`, so a differentiable family of protocols has a
differentiable `γ`. -/
theorem frozen_unitary_witness_eq
    {F : Matrix ((ιA' × εA) × (ιB' × εB)) (ιA × ιB) ℂ}
    {U : Matrix (ιA' × ιB') (ιA × ιB) ℂ} {γ : εA × εB → ℂ}
    (hU : U * Uᴴ = 1) (hF : F = insertResource ιA' ιB' γ * U)
    (kA : ιA') (kB : ιB') (e : εA × εB) :
    γ e = (F * Uᴴ) ((kA, e.1), (kB, e.2)) (kA, kB) := by
  have hFU : F * Uᴴ = insertResource ιA' ιB' γ := by
    rw [hF, Matrix.mul_assoc, hU, Matrix.mul_one]
  rw [hFU, insertResource_apply]
  simp

omit [DecidableEq ιA] [DecidableEq ιB] in
omit [Fintype εA] [Fintype εB] [DecidableEq εA] [DecidableEq εB] in
/-- The frozen environment vector of eq:frozen-unitary is **unique**.  The
existential of `lem:frozen-dilations` (i) therefore determines `γ` and does
not merely assert its existence. -/
theorem frozen_unitary_witness_unique [Nonempty ιA'] [Nonempty ιB']
    {F : Matrix ((ιA' × εA) × (ιB' × εB)) (ιA × ιB) ℂ}
    {U : Matrix (ιA' × ιB') (ιA × ιB) ℂ} {γ γ' : εA × εB → ℂ}
    (hU : U * Uᴴ = 1) (hF : F = insertResource ιA' ιB' γ * U)
    (hF' : F = insertResource ιA' ιB' γ' * U) : γ = γ' := by
  obtain ⟨kA⟩ := ‹Nonempty ιA'›
  obtain ⟨kB⟩ := ‹Nonempty ιB'›
  funext e
  rw [frozen_unitary_witness_eq hU hF kA kB e,
    ← frozen_unitary_witness_eq hU hF' kA kB e]

end Witness

end NLQCLean

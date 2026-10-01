/-
The exact two-sided outcome (rank-one PVM) task for a one-round protocol.
-/
import NLQCLean.Models.UnitaryTask

/-!
# The two-sided outcome task

The second of the paper's two exact target classes (snapshot §2.3,
L499-534).  An ordered rank-one PVM is an orthonormal basis
`Φ = (φ_1, …, φ_D)` of `H_A ⊗ H_B`, represented by the basis unitary
`M_Φ = Σ_i |φ_i⟩⟨i|` (**eq:basis-unitary**, L505-509).  In the two-sided
outcome task Alice and Bob finish with classical registers `O_A, O_B`, and
exactness is **eq:pvm-exactness** (L513-519):

  `Pr[O_A = O_B = i | ρ] = Tr(|φ_i⟩⟨φ_i| ρ)`,   `Pr[O_A ≠ O_B | ρ] = 0`

for every input state `ρ`. Both clauses are expressed for a general purified
isometry by `NLQCLean.TwoSidedExact` in `NLQCLean.Rigidity.FrozenDilation`.

## Why the task is *defined* at a specialized architecture

`eq:frozen-pvm` (L655-661) reads

  `F = Σ_{i=1}^{D} |i,i⟩ |ω_i⟩ ⟨φ_i|`,   `D = d_A d_B`,

so the outcome label `i` ranges over the *joint* index set of `H_A ⊗ H_B`,
and each laboratory holds a coherent copy of it.  Against the architecture of
`NLQCLean/Models/OneRound.lean` this type-checks only when

  `ι_{A'} = ι_{B'} = δ = ι_A × ι_B`,

which is exactly the paper's "for a measurement, `H_{X'}` includes the
coherent outcome label; any other output is included in `E_X`" (L445-446).
The task is defined at this instantiation.

At that instantiation the by-laboratory codomain of
`NLQCLean.PureProtocol.globalIsometry` is literally
`((ι_A × ι_B) × ε_A) × ((ι_A × ι_B) × ε_B)`, which is the index type of
`NLQCLean.exists_frozen_pvm` on the nose.  Part (ii) therefore needs **no**
regrouping bridge, in contrast with part (i), which needed
`NLQCLean.insertVector_eq_insertResource_submatrix`.

## Extraction of the frozen witnesses

As for the unitary branch, `NLQCLean.frozen_pvm_witness_eq` replaces the bare
existential of `lem:frozen-dilations` (ii) by the explicit formula

  `ω_i(e_A, e_B) = (F φ_i)_{((i,e_A),(i,e_B))}`,

which is linear in `F`, so that `prop:exact-velocity` can differentiate a
family of protocols.  `NLQCLean.frozen_pvm_witness_unique` records that the
witness is determined.
-/

namespace NLQCLean

open Matrix

section Task

variable {ιA ιB ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq εA] [DecidableEq εB]

/-- **The exact two-sided outcome task** for the architecture of
eq:global-isometry, at the measurement instantiation
`ι_{A'} = ι_{B'} = ι_A × ι_B` forced by eq:frozen-pvm (snapshot L445-446,
L655-661).

The condition itself is eq:pvm-exactness (L513-519), quantified over every
input state, in the already-formalized form `NLQCLean.TwoSidedExact`. -/
def PerformsPVM (η : ρA × ρB → ℂ)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ) (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix ((ιA × ιB) × εA) (κA × μB) ℂ)
    (DB : Matrix ((ιA × ιB) × εB) (κB × μA) ℂ)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) : Prop :=
  TwoSidedExact (globalIsometry η VA VB DA DB) M

/-- The exact two-sided outcome task for a pure-resource protocol whose two
logical output registers are the coherent joint outcome label. -/
def PureProtocol.PerformsPVM
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB (ιA × ιB) (ιA × ιB) εA εB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) : Prop :=
  TwoSidedExact P.globalIsometry M

theorem PureProtocol.performsPVM_iff
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB (ιA × ιB) (ιA × ιB) εA εB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    P.PerformsPVM M
      ↔ NLQCLean.PerformsPVM P.resource P.encA P.encB P.decA P.decB M :=
  Iff.rfl

/-- **`lem:frozen-dilations` (ii) for a protocol performing the two-sided
outcome task** (snapshot statement L654-661, `eq:frozen-pvm`).

The global isometry of eq:global-isometry factors as

  `F = C_ω M_Φ^† = Σ_i |i,i⟩ |ω_i⟩ ⟨φ_i|`

with every `ω_i` a unit vector on the discarded environment `E_A ⊗ E_B`, and
`C_ω` the flag isometry of eq:flag-isometry.  Both the factored form and the
entrywise sum of eq:frozen-pvm are given, as in the paper.

Together with `NLQCLean.PureProtocol.exists_frozen_of_performsUnitary` this
gives the two rigid forms `F = G T` for unitary and measurement protocols,
used in the cross-Gram argument. -/
theorem PureProtocol.exists_frozen_pvm
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB (ιA × ιB) (ιA × ιB) εA εB)
    {M : Matrix (ιA × ιB) (ιA × ιB) ℂ}
    (hM : Mᴴ * M = 1) (hM' : M * Mᴴ = 1) (htask : P.PerformsPVM M) :
    ∃ ω : (ιA × ιB) → εA × εB → ℂ, (∀ i, IsUnitVector (ω i)) ∧
      P.globalIsometry = flagIsometry ω * Mᴴ ∧
      ∀ (p : ((ιA × ιB) × εA) × ((ιA × ιB) × εB)) (j : ιA × ιB),
        P.globalIsometry p j
          = ∑ i, (if p.1.1 = i then (1 : ℂ) else 0)
                  * (if p.2.1 = i then 1 else 0)
                  * ω i (p.1.2, p.2.2) * star (M j i) :=
  _root_.NLQCLean.exists_frozen_pvm hM hM' htask

end Task

section Witness

variable {n δ εA εB : Type*}
variable [Fintype n] [Fintype δ] [Fintype εA] [Fintype εB]
variable [DecidableEq n] [DecidableEq δ] [DecidableEq εA] [DecidableEq εB]

omit [Fintype εA] [Fintype εB] [DecidableEq n] [DecidableEq εA] [DecidableEq εB] in
/-- **The frozen flag vectors are explicit linear functionals of `F`.**

If `F = C_ω M_Φ^†` (eq:frozen-pvm, snapshot L655-661) with `M_Φ` a basis
unitary, then

  `ω_i(e_A, e_B) = (F φ_i)_{((i,e_A),(i,e_B))}`,

where `φ_i` is the `i`-th column of `M_Φ`.  The right-hand side is linear in
`F`, so a differentiable family of protocols has differentiable flag vectors;
this is what `prop:exact-velocity` (L786-810) needs before it can form
`ω̇_i`. -/
theorem frozen_pvm_witness_eq
    {F : Matrix ((δ × εA) × (δ × εB)) n ℂ} {M : Matrix n δ ℂ}
    {ω : δ → εA × εB → ℂ}
    (hM : Mᴴ * M = 1) (hF : F = flagIsometry ω * Mᴴ) (i : δ) (e : εA × εB) :
    ω i e = (F *ᵥ pvmColumn M i) ((i, e.1), (i, e.2)) := by
  have hcol : Mᴴ *ᵥ pvmColumn M i = Pi.single i (1 : ℂ) := by
    funext k
    have hk : (Mᴴ *ᵥ pvmColumn M i) k = (Mᴴ * M) k i := rfl
    rw [hk, hM, Matrix.one_apply, Pi.single_apply]
  rw [hF, ← Matrix.mulVec_mulVec, hcol]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

omit [Fintype εA] [Fintype εB] [DecidableEq n] [DecidableEq εA] [DecidableEq εB] in
/-- The flag vectors of eq:frozen-pvm are **unique**.  The existential of
`lem:frozen-dilations` (ii) therefore determines `ω`. -/
theorem frozen_pvm_witness_unique
    {F : Matrix ((δ × εA) × (δ × εB)) n ℂ} {M : Matrix n δ ℂ}
    {ω ω' : δ → εA × εB → ℂ}
    (hM : Mᴴ * M = 1) (hF : F = flagIsometry ω * Mᴴ)
    (hF' : F = flagIsometry ω' * Mᴴ) : ω = ω' := by
  funext i e
  rw [frozen_pvm_witness_eq hM hF i e, ← frozen_pvm_witness_eq hM hF' i e]

end Witness

end NLQCLean

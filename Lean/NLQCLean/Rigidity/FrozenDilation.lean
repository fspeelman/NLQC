/-
Frozen target dilations: the two rigid forms of a purified global isometry.
-/
import NLQCLean.Models.Channels
import NLQCLean.Rigidity.Compression
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic

/-!
# Frozen target dilations

This is `lem:frozen-dilations` of the snapshot (statement L643-662, proof
L664-679); "frozen" is defined at L640-642 as *the discarded environment is
independent of the unknown logical input* (it may still vary when the
protocol itself varies).

* (i) `NLQCLean.exists_frozen_unitary` — if the induced channel of `F` is
  `Ad_U` then `F = J_γ U` for a **single** unit vector `γ`
  (eq:frozen-unitary, L649-653).
* (ii) `NLQCLean.exists_frozen_pvm` — if `F` performs the two-sided outcome
  task for the basis `Φ` (eq:pvm-exactness, L513-519) then
  `F = C_ω M_Φ^† = Σ_i |i,i⟩|ω_i⟩⟨φ_i|` for unit vectors `ω_i`
  (eq:frozen-pvm, L655-661).

## Purified isometries and physical protocols

The paper's `F` is the global isometry `F = (D_A ⊗ D_B) Ex (V_A ⊗ V_B) J_η`
of eq:global-isometry (L457-461). Its architecture record and the
instantiation of the unitary freezing theorem are in
`NLQCLean.Models.OneRound`.

Both parts below are stated for a general purified isometry `F`
carrying exactly the hypotheses the paper's proof uses:

* part (i): `channelOf F = adConj U`, i.e. "the induced channel is `Ad_U`";
* part (ii): two-sided outcome exactness for every input state.

The proofs use only the induced channel (obtained by discarding the
environment, L461-463) or the outcome statistics. They therefore apply to
any purified isometry with these properties, including the physical
one-round protocol.

## Index conventions

Part (ii) uses the **by-laboratory** register grouping fixed by the paper at
L454 and used throughout `NLQCLean/Rigidity/Compression.lean`: Alice holds
`(outcome label, private environment)` and so does Bob, so the codomain index
is `(δ × ε_A) × (δ × ε_B)`.  With that grouping the `C_ω` of eq:frozen-pvm is
*literally* `NLQCLean.flagIsometry` (eq:flag-isometry, L605-611); no second
copy is defined, and `flag_compression_mem_diagonal` applies verbatim to the
`C_ω` produced here.  The paper's block `F_{ab}` is `NLQCLean.outcomeBlock F a
b`, the block at outcome labels `(a,b)` whose remaining row index is the pair
of environments.

The domain index `n` of `H_A ⊗ H_B` and the outcome-label index `δ` are kept
distinct, as in the paper: `M_Φ = Σ_i |φ_i⟩⟨i|` is `M : Matrix n δ ℂ`
(eq:basis-unitary, L505-509) and its `i`-th column is `φ_i`.  The conclusion
`F = flagIsometry ω * Mᴴ` realizes `T = M_Φ^†` with the **diagonal output
algebra on the left** of `T` (L681-685): the label registers are the outermost
row index of `F`, so the left factor `C_ω` is exactly where `𝔱^D` acts.

Part (i) instead uses the system-then-environment grouping
`F : Matrix (κ × ε) ι ℂ`, which is forced by the signature of
`NLQCLean.channelOf` (logical input `ι`, retained output `κ`, discarded
environment `ε`).  `NLQCLean.insertVector κ γ` is the minimal `J_γ` for that
grouping and is deliberately local to this module.  In the by-laboratory
grouping the paper's `J_γ` is `NLQCLean.insertResource ι_{A'} ι_{B'} γ` with
the resource types instantiated to the two private environments
`(ε_A, ε_B)`; bridging `insertVector` to `insertResource` across the
middle-two-transposition regrouping
`(ι_{A'} × ι_{B'}) × (ε_A × ε_B) ≃ (ι_{A'} × ε_A) × (ι_{B'} × ε_B)`
is proved by `insertVector_eq_insertResource_submatrix` in
`NLQCLean.Models.OneRound`.

## Proof by matrix coefficients

The paper's proof of (i) invokes uniqueness of the minimal Stinespring
dilation of the identity channel, and its proof of (ii) invokes a polar
decomposition. Here both conclusions follow directly from matrix coefficients:

* (i) `G = F Uᴴ` has `channelOf G = id`.  Testing on the matrix units gives
  `Σ_e G_{(k,e),i} conj(G_{(k',e),i'}) = δ_{ki} δ_{k'i'}`.  Taking `k = k'`,
  `i = i'`, `k ≠ i` kills the off-diagonal columns; taking `k = i`,
  `k' = i'` gives `⟪v_i, v_{i'}⟫ = 1` for the diagonal columns
  `v_i = G_{(i,·),i}`, whence `‖v_i - v_{i'}‖² = 1 - 1 - 1 + 1 = 0` by
  expanding the norm.  So all `v_i` are one and the same unit vector `γ`.
* (ii) Exactness at the pure states `|φ_j⟩⟨φ_j|` and `|e_j⟩⟨e_j|` gives
  `F_{ab} = 0` for `a ≠ b` and `F_{ii} φ_j = 0` for `j ≠ i`; expanding the
  standard basis in the basis `Φ` then gives `F_{ii} = ω_i φ_i^†` directly
  with `ω_i = F_{ii} φ_i`, and `‖ω_i‖ = 1` from exactness at `|φ_i⟩⟨φ_i|`.

`Nonempty ι` is required in (i), and is genuinely needed: over an empty
logical input space there is no vector `γ` to produce.
-/

namespace NLQCLean

open Matrix
open scoped ComplexOrder

section UnitVector

variable {ε : Type*} [Fintype ε]

/-- A finite family of complex numbers whose squared moduli sum to zero
vanishes. -/
theorem eq_zero_of_sum_mul_star_eq_zero {z : ε → ℂ}
    (h : ∑ e, z e * star (z e) = 0) (e : ε) : z e = 0 := by
  have hz : z ⬝ᵥ star z = 0 := by simpa [dotProduct] using h
  exact congrFun (dotProduct_self_star_eq_zero.1 hz) e

theorem eq_zero_of_sum_normSq_eq_zero {z : ε → ℂ}
    (h : ∑ e, Complex.normSq (z e) = 0) (e : ε) : z e = 0 := by
  refine eq_zero_of_sum_mul_star_eq_zero ?_ e
  rw [sum_mul_star_eq_normSq, h, Complex.ofReal_zero]

end UnitVector

/-! ## Part (i): the unitary branch -/

section FrozenUnitary

/-- The frozen resource insertion `J_γ ψ = ψ ⊗ γ` (snapshot L449-454) in the
system-then-environment grouping forced by `NLQCLean.channelOf`.  This is a
deliberately minimal local definition; see the module docstring for its
relation to `NLQCLean.insertResource`. -/
def insertVector (κ : Type*) [DecidableEq κ] {ε : Type*} (γ : ε → ℂ) :
    Matrix (κ × ε) κ ℂ :=
  Matrix.of fun p k => (if p.1 = k then 1 else 0) * γ p.2

@[simp] theorem insertVector_apply {κ ε : Type*} [DecidableEq κ] (γ : ε → ℂ)
    (p : κ × ε) (k : κ) :
    insertVector κ γ p k = (if p.1 = k then 1 else 0) * γ p.2 := rfl

/-- `J_γ` is an isometry when `γ` is a unit vector.  `prop:exact-velocity`
needs this to know that `B = Dec† J_γ` is an isometry (snapshot L820-824).
Instance of `NLQCLean.isIsometry_of_unit_columns` with a trivial row
splitting and `φ = id`. -/
theorem isIsometry_insertVector {κ ε : Type*} [Fintype κ] [Fintype ε]
    [DecidableEq κ] (γ : ε → ℂ) (hγ : IsUnitVector γ) :
    IsIsometry (insertVector κ γ) := by
  refine isIsometry_of_unit_columns (Equiv.refl (κ × ε)) id Function.injective_id
    (fun _ => γ) (fun _ => hγ) ?_
  intro p k
  rw [insertVector_apply]
  rfl

variable {ι κ ε : Type*} [Fintype ι] [Fintype κ] [Fintype ε]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ε]

omit [DecidableEq ε] in
/-- **`lem:frozen-dilations` (i)** (snapshot statement L649-653, proof
L665-668; eq:frozen-unitary).

If the channel induced by the purified isometry `F` is `Ad_U` for a unitary
`U`, then there is a unit vector `γ`, **independent of the logical input**,
with `F = J_γ U`.  That `γ` is a constant and not a function of the input is
the whole content of the lemma; the paper explicitly allows it to vary when
the protocol varies (L640-642), which is what makes `γ̇ ≠ 0` possible in
`prop:exact-velocity`.

Stated for a general purified isometry; see the module docstring for why this
is faithful to eq:global-isometry. -/
theorem exists_frozen_unitary [Nonempty ι]
    {F : Matrix (κ × ε) ι ℂ} {U : Matrix κ ι ℂ}
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hF : channelOf F = adConj U) :
    ∃ γ : ε → ℂ, IsUnitVector γ ∧ F = insertVector κ γ * U := by
  -- The retained output register is nonempty, because `U` is an isometry out
  -- of a nonempty logical space.
  have hκ : Nonempty κ := by
    rw [← not_isEmpty_iff]
    intro hcon
    have := hcon
    obtain ⟨i⟩ := ‹Nonempty ι›
    have h1 : (Uᴴ * U) i i = (1 : Matrix ι ι ℂ) i i := by rw [hU]
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    simp at h1
  obtain ⟨i₀⟩ := hκ
  -- `G = F Uᴴ` dilates the identity channel.
  set G : Matrix (κ × ε) κ ℂ := F * Uᴴ with hG
  have hGU : G * U = F := by rw [hG, Matrix.mul_assoc, hU, Matrix.mul_one]
  have hid : ∀ ρ : Matrix κ κ ℂ, channelOf G ρ = ρ := by
    intro ρ
    have hexp : G * ρ * Gᴴ = F * (Uᴴ * ρ * U) * Fᴴ := by
      rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      simp [Matrix.mul_assoc]
    have hstep : channelOf G ρ = channelOf F (Uᴴ * ρ * U) := by
      rw [channelOf_apply, channelOf_apply, hexp]
    rw [hstep, hF, adConj_apply]
    calc U * (Uᴴ * ρ * U) * Uᴴ = (U * Uᴴ) * ρ * (U * Uᴴ) := by
          simp [Matrix.mul_assoc]
      _ = ρ := by rw [hU']; simp
  -- Entrywise form of `channelOf G = id`, tested on the matrix units.
  have hL : ∀ a a' i i' : κ,
      channelOf G (Matrix.single i i' (1 : ℂ)) a a'
        = ∑ e, G (a, e) i * star (G (a', e) i') := by
    intro a a' i i'
    simp only [channelOf_apply, ptraceB_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and]
  have key : ∀ a a' i i' : κ,
      (∑ e, G (a, e) i * star (G (a', e) i'))
        = (if i = a then (1 : ℂ) else 0) * (if i' = a' then 1 else 0) := by
    intro a a' i i'
    rw [← hL a a' i i', hid, Matrix.single_apply]
    by_cases h1 : i = a <;> by_cases h2 : i' = a' <;> simp [h1, h2]
  -- Off-diagonal columns vanish.
  have hoff : ∀ a k : κ, a ≠ k → ∀ e, G (a, e) k = 0 := by
    intro a k hak e
    have h := key a a k k
    rw [if_neg (fun h' : k = a => hak h'.symm)] at h
    refine eq_zero_of_sum_mul_star_eq_zero (z := fun e => G (a, e) k) ?_ e
    simpa using h
  -- The diagonal columns are pairwise unit and pairwise "aligned".
  set v : κ → ε → ℂ := fun i e => G (i, e) i with hv
  have hvv : ∀ i i' : κ, ∑ e, v i e * star (v i' e) = 1 := by
    intro i i'
    have h := key i i' i i'
    simpa [hv] using h
  -- Hence they all coincide.
  have hconst : ∀ i i' : κ, ∀ e, v i e = v i' e := by
    intro i i' e
    have hexpand : ∀ e, (v i e - v i' e) * star (v i e - v i' e)
        = v i e * star (v i e) - v i e * star (v i' e)
          - v i' e * star (v i e) + v i' e * star (v i' e) := by
      intro e
      rw [star_sub]; ring
    have hsum : ∑ e, (v i e - v i' e) * star (v i e - v i' e) = 0 := by
      rw [Finset.sum_congr rfl fun e _ => hexpand e]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        hvv i i, hvv i i', hvv i' i, hvv i' i']
      ring
    exact sub_eq_zero.1 (eq_zero_of_sum_mul_star_eq_zero hsum e)
  refine ⟨v i₀, (isUnitVector_iff_sum _).2 (hvv i₀ i₀), ?_⟩
  rw [← hGU]
  congr 1
  ext p k
  obtain ⟨a, e⟩ := p
  rcases eq_or_ne a k with rfl | hne
  · have hiv : insertVector κ (v i₀) (a, e) a = v i₀ e := by simp [insertVector]
    rw [hiv]
    exact hconst a i₀ e
  · have hiv : insertVector κ (v i₀) (a, e) k = 0 := by simp [insertVector, hne]
    rw [hiv]
    exact hoff a k hne e

end FrozenUnitary

/-! ## Part (ii): the two-sided outcome (PVM) branch -/

section FrozenPVM

variable {n δ εA εB : Type*}
variable [Fintype n] [Fintype δ] [Fintype εA] [Fintype εB]
variable [DecidableEq n] [DecidableEq δ] [DecidableEq εA] [DecidableEq εB]

/-- A density matrix on `ℂ^n`: this is the paper's "input state `ρ`" of
eq:pvm-exactness (snapshot L513-519). -/
def IsState (ρ : Matrix n n ℂ) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

/-- The pure state `|x⟩⟨x|`. -/
def pureState (x : n → ℂ) : Matrix n n ℂ := Matrix.vecMulVec x (star x)

omit [Fintype n] [DecidableEq n] in
@[simp] theorem pureState_apply (x : n → ℂ) (j k : n) :
    pureState x j k = x j * star (x k) := rfl

omit [DecidableEq n] in
theorem isState_pureState {x : n → ℂ} (hx : IsUnitVector x) :
    IsState (pureState x) := by
  refine ⟨Matrix.posSemidef_vecMulVec_self_star x, ?_⟩
  have htr : (pureState x).trace = ∑ j, x j * star (x j) := rfl
  rw [htr, (isUnitVector_iff_sum x).1 hx]

/-- The `i`-th column `φ_i` of the basis unitary `M_Φ = Σ_i |φ_i⟩⟨i|`
(eq:basis-unitary, snapshot L505-509). -/
def pvmColumn (M : Matrix n δ ℂ) (i : δ) : n → ℂ := fun j => M j i

omit [Fintype n] [Fintype δ] [DecidableEq n] [DecidableEq δ] in
@[simp] theorem pvmColumn_apply (M : Matrix n δ ℂ) (i : δ) (j : n) :
    pvmColumn M i j = M j i := rfl

/-- The rank-one projector `|φ_i⟩⟨φ_i|` of the PVM. -/
def pvmProj (M : Matrix n δ ℂ) (i : δ) : Matrix n n ℂ := pureState (pvmColumn M i)

/-- The block `F_{ab}` of `F` at the pair of classical outcome labels `(a,b)`
(snapshot L670-673).  With the by-laboratory grouping the remaining row index
is the pair of private environments. -/
def outcomeBlock (F : Matrix ((δ × εA) × (δ × εB)) n ℂ) (a b : δ) :
    Matrix (εA × εB) n ℂ :=
  Matrix.of fun e j => F ((a, e.1), (b, e.2)) j

omit [Fintype n] [Fintype δ] [Fintype εA] [Fintype εB] [DecidableEq n] [DecidableEq δ] [DecidableEq εA] [DecidableEq εB] in
@[simp] theorem outcomeBlock_apply (F : Matrix ((δ × εA) × (δ × εB)) n ℂ)
    (a b : δ) (e : εA × εB) (j : n) :
    outcomeBlock F a b e j = F ((a, e.1), (b, e.2)) j := rfl

/-- The outcome probability `p_ρ(a,b) = Tr(F_{ab} ρ F_{ab}^†)` of the
two-sided outcome task. -/
def outcomeProb (F : Matrix ((δ × εA) × (δ × εB)) n ℂ) (ρ : Matrix n n ℂ)
    (a b : δ) : ℂ :=
  (outcomeBlock F a b * ρ * (outcomeBlock F a b)ᴴ).trace

/-- **eq:pvm-exactness** (snapshot L513-519): the protocol `F` performs the
two-sided outcome task for the ordered rank-one PVM with basis unitary `M`.
Both clauses are quantified over **every input state `ρ`**, as in the paper,
and the second clause is the paper's `Pr[O_A ≠ O_B | ρ] = 0` in its literal
summed form. -/
structure TwoSidedExact (F : Matrix ((δ × εA) × (δ × εB)) n ℂ) (M : Matrix n δ ℂ) :
    Prop where
  /-- `Pr[O_A = O_B = i | ρ] = Tr(|φ_i⟩⟨φ_i| ρ)`. -/
  agree : ∀ ρ : Matrix n n ℂ, IsState ρ → ∀ i : δ,
    outcomeProb F ρ i i = (pvmProj M i * ρ).trace
  /-- `Pr[O_A ≠ O_B | ρ] = 0`. -/
  disagree : ∀ ρ : Matrix n n ℂ, IsState ρ →
    ∑ p ∈ Finset.univ.filter (fun p : δ × δ => p.1 ≠ p.2),
      outcomeProb F ρ p.1 p.2 = 0

omit [Fintype δ] [DecidableEq δ] [DecidableEq εA] [DecidableEq εB] in
omit [DecidableEq n] in
/-- The outcome probability at a pure state is `‖F_{ab} x‖²`. -/
theorem outcomeProb_pureState (F : Matrix ((δ × εA) × (δ × εB)) n ℂ)
    (x : n → ℂ) (a b : δ) :
    outcomeProb F (pureState x) a b
      = ((∑ e, Complex.normSq ((outcomeBlock F a b *ᵥ x) e) : ℝ) : ℂ) := by
  rw [← sum_mul_star_eq_normSq]
  simp only [outcomeProb, Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  set B := outcomeBlock F a b with hB
  have hrow : ∀ k : n, (B * pureState x) e k = (B *ᵥ x) e * star (x k) := by
    intro k
    rw [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [pureState_apply]; ring
  rw [Matrix.mul_apply]
  simp only [hrow, Matrix.conjTranspose_apply, mul_assoc, ← Finset.mul_sum]
  congr 1
  rw [Matrix.mulVec, dotProduct, star_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [star_mul, mul_comm]

omit [Fintype δ] [DecidableEq n] [DecidableEq δ] in
/-- `Tr(|φ_i⟩⟨φ_i| · |x⟩⟨x|) = |⟨φ_i, x⟩|²`. -/
theorem trace_pvmProj_pureState (M : Matrix n δ ℂ) (i : δ) (x : n → ℂ) :
    (pvmProj M i * pureState x).trace
      = ((Complex.normSq (∑ j, star (M j i) * x j) : ℝ) : ℂ) := by
  have hsum : (pvmProj M i * pureState x).trace
      = (∑ k, star (M k i) * x k) * star (∑ j, star (M j i) * x j) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, pvmProj,
      pureState_apply, pvmColumn_apply]
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [star_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul, star_star]
    ring
  rw [hsum, ← starRingEnd_apply, Complex.mul_conj]

section Exact

variable {F : Matrix ((δ × εA) × (δ × εB)) n ℂ} {M : Matrix n δ ℂ}

omit [DecidableEq εA] [DecidableEq εB] in
omit [DecidableEq n] in
/-- Off-diagonal blocks annihilate every unit vector. -/
theorem outcomeBlock_mulVec_eq_zero_of_ne (hex : TwoSidedExact F M)
    {x : n → ℂ} (hx : IsUnitVector x) {a b : δ} (hab : a ≠ b) :
    ∀ e, (outcomeBlock F a b *ᵥ x) e = 0 := by
  have hsum := hex.disagree (pureState x) (isState_pureState hx)
  simp only [outcomeProb_pureState] at hsum
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero] at hsum
  have hnonneg : ∀ p ∈ Finset.univ.filter (fun p : δ × δ => p.1 ≠ p.2),
      (0 : ℝ) ≤ ∑ e, Complex.normSq ((outcomeBlock F p.1 p.2 *ᵥ x) e) :=
    fun p _ => Finset.sum_nonneg fun e _ => Complex.normSq_nonneg _
  have hmem : (a, b) ∈ Finset.univ.filter (fun p : δ × δ => p.1 ≠ p.2) := by
    simp [hab]
  exact eq_zero_of_sum_normSq_eq_zero
    ((Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum (a, b) hmem)

omit [DecidableEq εA] [DecidableEq εB] in
/-- **Off-diagonal blocks vanish** (snapshot L672-676): `F_{ab} = 0` for
`a ≠ b`. -/
theorem outcomeBlock_eq_zero_of_ne (hex : TwoSidedExact F M) {a b : δ} (hab : a ≠ b) :
    outcomeBlock F a b = 0 := by
  ext e j
  have hunit : IsUnitVector (Pi.single j (1 : ℂ)) := by
    simp [IsUnitVector, Pi.single_apply, apply_ite Complex.normSq]
  have h := outcomeBlock_mulVec_eq_zero_of_ne hex hunit hab e
  rw [Matrix.mulVec, dotProduct] at h
  rw [Matrix.zero_apply, ← h, Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · intro hj; exact absurd (Finset.mem_univ j) hj

omit [DecidableEq εA] [DecidableEq εB] in
omit [DecidableEq n] in
/-- The squared norm of `F_{ii} x` is `|⟨φ_i, x⟩|²` for every unit `x`. -/
theorem sum_normSq_diag_block (hex : TwoSidedExact F M) {x : n → ℂ}
    (hx : IsUnitVector x) (i : δ) :
    ∑ e, Complex.normSq ((outcomeBlock F i i *ᵥ x) e)
      = Complex.normSq (∑ j, star (M j i) * x j) := by
  have h := hex.agree (pureState x) (isState_pureState hx) i
  rw [outcomeProb_pureState, trace_pvmProj_pureState] at h
  exact_mod_cast h

end Exact

section BasisUnitary

variable {M : Matrix n δ ℂ}

omit [Fintype δ] [DecidableEq n] in
/-- `⟨φ_i, φ_i⟩ = 1`: the columns of a basis unitary are normalized. -/
theorem pvmColumn_inner_self (hM : Mᴴ * M = 1) (i : δ) :
    ∑ k, star (M k i) * pvmColumn M i k = 1 := by
  have h : (Mᴴ * M) i i = (1 : Matrix δ δ ℂ) i i := by rw [hM]
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simp only [Matrix.conjTranspose_apply] at h
  simpa using h

omit [Fintype δ] [DecidableEq n] in
/-- `⟨φ_i, φ_j⟩ = 0` for `j ≠ i`: distinct basis vectors are orthogonal. -/
theorem pvmColumn_inner_eq_zero (hM : Mᴴ * M = 1) {i j : δ} (hij : j ≠ i) :
    ∑ k, star (M k i) * pvmColumn M j k = 0 := by
  have h : (Mᴴ * M) i j = (1 : Matrix δ δ ℂ) i j := by rw [hM]
  rw [Matrix.mul_apply, Matrix.one_apply_ne (Ne.symm hij)] at h
  simp only [Matrix.conjTranspose_apply] at h
  simpa using h

omit [Fintype δ] [DecidableEq n] in
/-- The columns of a basis unitary are unit vectors. -/
theorem isUnitVector_pvmColumn (hM : Mᴴ * M = 1) (i : δ) :
    IsUnitVector (pvmColumn M i) := by
  refine (isUnitVector_iff_sum _).2 ?_
  rw [← pvmColumn_inner_self hM i]
  exact Finset.sum_congr rfl fun k _ => by
    simp only [pvmColumn_apply]
    exact mul_comm _ _

end BasisUnitary

omit [DecidableEq εA] [DecidableEq εB] in
/-- **`lem:frozen-dilations` (ii)** (snapshot statement L654-661, proof
L670-678; eq:frozen-pvm).

If the purified isometry `F` performs the two-sided outcome task for the
ordered rank-one PVM with basis unitary `M = M_Φ`, then there are unit
vectors `ω_i` with `F = C_ω M_Φ^† = Σ_i |i,i⟩|ω_i⟩⟨φ_i|`, where `C_ω` is the
flag isometry `NLQCLean.flagIsometry` of eq:flag-isometry.  Both the factored
form and the explicit entrywise sum of eq:frozen-pvm are stated, as in the
paper.

Stated for a general purified isometry; see the module docstring for why this
is faithful to eq:global-isometry, and for the register order that makes
`T = M_Φ^†` carry the diagonal output algebra on its left (L681-685). -/
theorem exists_frozen_pvm
    {F : Matrix ((δ × εA) × (δ × εB)) n ℂ} {M : Matrix n δ ℂ}
    (hM : Mᴴ * M = 1) (hM' : M * Mᴴ = 1) (hex : TwoSidedExact F M) :
    ∃ ω : δ → εA × εB → ℂ, (∀ i, IsUnitVector (ω i)) ∧
      F = flagIsometry ω * Mᴴ ∧
      ∀ (p : (δ × εA) × (δ × εB)) (j : n),
        F p j = ∑ i, (if p.1.1 = i then (1 : ℂ) else 0)
                      * (if p.2.1 = i then 1 else 0)
                      * ω i (p.1.2, p.2.2) * star (M j i) := by
  classical
  -- `‖ω_i‖ = 1`, with `ω_i = F_{ii} φ_i`.
  have hunit : ∀ i : δ, IsUnitVector (outcomeBlock F i i *ᵥ pvmColumn M i) := by
    intro i
    have h := sum_normSq_diag_block hex (isUnitVector_pvmColumn hM i) i
    rw [pvmColumn_inner_self hM i, Complex.normSq_one] at h
    exact h
  -- `F_{ii}` annihilates every other basis vector.
  have hkill : ∀ i j : δ, j ≠ i →
      ∀ e, (outcomeBlock F i i *ᵥ pvmColumn M j) e = 0 := by
    intro i j hij e
    have h := sum_normSq_diag_block hex (isUnitVector_pvmColumn hM j) i
    rw [pvmColumn_inner_eq_zero hM hij, Complex.normSq_zero] at h
    exact eq_zero_of_sum_normSq_eq_zero h e
  -- Expanding the standard basis in the orthonormal basis `Φ`.
  have hexpand : ∀ (B : Matrix (εA × εB) n ℂ) (e : εA × εB) (j : n),
      B e j = ∑ k, star (M j k) * (B *ᵥ pvmColumn M k) e := by
    intro B e j
    have hstep : ∀ k : δ, star (M j k) * (B *ᵥ pvmColumn M k) e
        = ∑ l, B e l * (M l k * star (M j k)) := by
      intro k
      rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [pvmColumn_apply]; ring
    have hcol : ∀ l : n, ∑ k, B e l * (M l k * star (M j k))
        = B e l * (1 : Matrix n n ℂ) l j := by
      intro l
      rw [← hM', Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [Matrix.conjTranspose_apply]
    have hfin : ∑ l, B e l * (1 : Matrix n n ℂ) l j
        = B e j * (1 : Matrix n n ℂ) j j :=
      Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
        (fun l _ hl => by rw [Matrix.one_apply_ne hl, mul_zero])
    rw [Finset.sum_congr rfl fun k _ => hstep k, Finset.sum_comm,
      Finset.sum_congr rfl fun l _ => hcol l, hfin, Matrix.one_apply_eq, mul_one]
  -- The diagonal blocks are the rank-one matrices `|ω_i⟩⟨φ_i|`.
  have hdiag : ∀ (i : δ) (e : εA × εB) (j : n),
      outcomeBlock F i i e j
        = star (M j i) * (outcomeBlock F i i *ᵥ pvmColumn M i) e := by
    intro i e j
    have hs : ∑ k, star (M j k) * (outcomeBlock F i i *ᵥ pvmColumn M k) e
        = star (M j i) * (outcomeBlock F i i *ᵥ pvmColumn M i) e :=
      Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
        (fun k _ hk => by rw [hkill i k hk e, mul_zero])
    rw [hexpand (outcomeBlock F i i) e j, hs]
  -- The factored form `F = C_ω M_Φ^†`.
  have hfact : F
      = flagIsometry (fun i => outcomeBlock F i i *ᵥ pvmColumn M i) * Mᴴ := by
    ext p j
    obtain ⟨⟨a, eA⟩, ⟨b, eB⟩⟩ := p
    rcases eq_or_ne a b with rfl | hab
    · have hs : ∑ i, flagIsometry (fun i => outcomeBlock F i i *ᵥ pvmColumn M i)
            ((a, eA), (a, eB)) i * Mᴴ i j
          = flagIsometry (fun i => outcomeBlock F i i *ᵥ pvmColumn M i)
              ((a, eA), (a, eB)) a * Mᴴ a j :=
        Finset.sum_eq_single_of_mem a (Finset.mem_univ a)
          (fun k _ hk => by simp [Ne.symm hk])
      have hterm : flagIsometry (fun i => outcomeBlock F i i *ᵥ pvmColumn M i)
            ((a, eA), (a, eB)) a * Mᴴ a j
          = star (M j a) * (outcomeBlock F a a *ᵥ pvmColumn M a) (eA, eB) := by
        simp [mul_comm]
      rw [Matrix.mul_apply, hs, hterm]
      exact hdiag a (eA, eB) j
    · have hb := outcomeBlock_eq_zero_of_ne hex hab
      have hzero : F ((a, eA), (b, eB)) j = 0 := by
        have h2 : outcomeBlock F a b (eA, eB) j = 0 := by
          simp only [hb, Matrix.zero_apply]
        exact h2
      rw [Matrix.mul_apply, hzero]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      rcases eq_or_ne a k with rfl | hak
      · simp [Ne.symm hab]
      · simp [hak]
  refine ⟨fun i => outcomeBlock F i i *ᵥ pvmColumn M i, hunit, hfact, fun p j => ?_⟩
  have hpj : F p j
      = (flagIsometry (fun i => outcomeBlock F i i *ᵥ pvmColumn M i) * Mᴴ) p j := by
    conv_lhs => rw [hfact]
  rw [hpj, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun i _ => by
    rw [flagIsometry_apply, Matrix.conjTranspose_apply]


end FrozenPVM

end NLQCLean
